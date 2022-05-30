use crate::*;

#[derive(Clone, Debug)]
pub struct Graph<L: Language> {
    // TODO: Analysis?
    // pub analysis: N,
    memo: HashMap<L, Id>,
    nodes: HashMap<Id, Node<L>>,
    next_id: usize,
    roots: Vec<Id>,
}

#[derive(Clone, Debug)]
pub struct Node<L: Language> {
    pub n: L,
    pub(crate) parents: Vec<Id>,
}

impl<L: Language> Default for Graph<L> {
    fn default() -> Self {
        Graph {
            memo: Default::default(),
            nodes: Default::default(),
            next_id: 0,
            roots: Default::default(),
        }
    }
}

impl<L: Language> std::ops::Index<Id> for Graph<L> {
    type Output = L;
    fn index(&self, id: Id) -> &Self::Output {
        &self.nodes.get(&id)
            .unwrap_or_else(|| panic!("Invalid id {}", id))
            .n
    }
}

impl<L: Language> std::ops::IndexMut<Id> for Graph<L> {
    fn index_mut(&mut self, id: Id) -> &mut Self::Output {
        &mut self.nodes.get_mut(&id)
            .unwrap_or_else(|| panic!("Invalid id {}", id))
            .n
    }
}

impl<L: Language> Graph<L> {
    pub fn from_dfg(dfg: &RecExpr<L>, roots: Vec<Id>) -> Self {
        let mut g = Graph::default();
        let nodes = dfg.as_ref();
        let mut ids = Vec::with_capacity(nodes.len());
        for node in nodes {
            ids.push(g.add(node.clone().map_children(|i| {
                ids[usize::from(i)]
            })));
        }
        for root in roots {
            g.add_root(ids[usize::from(root)]);
        }
        g
    }

    pub fn nodes(&self) -> impl ExactSizeIterator<Item = (&Id, &Node<L>)> {
        self.nodes.iter()
    }

    pub fn nodes_mut(&mut self) -> impl ExactSizeIterator<Item = (&Id, &mut Node<L>)> {
        self.nodes.iter_mut()
    }

    pub fn add_root(&mut self, id: Id) {
        self.roots.push(id);
    }

    pub fn add(&mut self, node: L) -> Id {
        if let Some(existing_id) = self.lookup(&node) {
            existing_id
        } else {
            let id = self.next_id();
            assert!(self.nodes.insert(id, Node {
                n: node.clone(), parents: Vec::new(),
            }).is_none());
            assert!(self.memo.insert(node.clone(), id).is_none());

            node.for_each(|c| {
                let parents = &mut self.nodes.get_mut(&c)
                    .unwrap_or_else(|| panic!("Invalid child id"))
                    .parents;
                parents.push(id);
                // TODO: dedup?
            });

            id
        }
    }

    fn next_id(&mut self) -> Id {
        let id = Id::from(self.next_id);
        self.next_id = self.next_id.checked_add(1)
            .unwrap_or_else(|| panic!("Id overflow"));
        id
    }

    pub fn lookup(&self, node: &L) -> Option<Id> {
        self.memo.get(node).copied()
    }

    // replace original with the given pattern instantiation
    pub fn replace(&mut self, original: Id, ast: &PatternAst<L>, subst: &Subst) {
        // 0. replace original with dummy
        let replacement_dummy = self.next_id();
        let mut ori_n = self.nodes.remove(&original)
            .unwrap_or_else(|| panic!("Invalid id"));
        let replacement_dummy_parents = &mut Vec::with_capacity(ori_n.parents.len());
        self.move_parents(&mut ori_n.parents, original,
                          replacement_dummy_parents, replacement_dummy);
        assert!(self.nodes.insert(original, ori_n).is_none());

        // println!("replacement dummy: {:?}", self);

        // 1. create replacement
        let ast = ast.as_ref();
        let mut ids = vec![0.into(); ast.len()];
        for (i, pat_node) in ast.iter().enumerate() {
            let id = match pat_node {
                ENodeOrVar::Var(w) => subst[*w],
                ENodeOrVar::ENode(e) => {
                    let n = e.clone().map_children(|c| ids[usize::from(c)]);
                    self.add(n)
                }
            };
            ids[i] = id;
        }
        let replacement = *ids.last().unwrap();

        // println!("replacement constructed: {:?}", self);

        if original == replacement {
            println!("WARNING: weird rule?");
            return
        }

        // 2. replace dummy with replacement
        let mut rep_n = self.nodes.remove(&replacement)
            .unwrap_or_else(|| panic!("Invalid id"));
        self.move_parents(replacement_dummy_parents, replacement_dummy,
                          &mut rep_n.parents, replacement);
        assert!(self.nodes.insert(replacement, rep_n).is_none());

        println!("replacement inserted: {:?}", self);

        // 3. restore hash-consing invariant broken by dummy
        let canonicalized = self.merge_upwards(vec![replacement]);

        println!("merged upwards: {:?}", self);

        // 4. collect garbage
        if canonicalized.get(&original).is_none() {
            self.may_remove(original);
        }

        println!("garbage collected: {:?}", self);

        debug_assert!(self.check());
    }

    fn move_parents(&mut self,
        parents_of: &mut Vec<Id>, of: Id, 
        parents_to: &mut Vec<Id>, to: Id
    ) {
        for p in parents_of.drain(..) {
            let n = &mut self.nodes.get_mut(&p).unwrap().n;
            let n_bak = n.clone();
            assert!(self.memo.remove(n) == Some(p));
            n.for_each_mut(|pc| {
                if *pc == of { *pc = to }
            });
            println!("moving parents, {:?}: {:?} --> {:?}", p, n_bak, n);
            // NOTE: this may trigger memo conflict, requiring upward merge afterwards
            // (if insert returns None)
            self.memo.insert(n.clone(), p);
            parents_to.push(p);
        }
        for r in &mut self.roots[..] {
            if *r == of { *r = to }
        }
    }

    fn may_remove(&mut self, id: Id) {
        let n = self.nodes.get(&id)
            .unwrap_or_else(|| panic!("Invalid id"));
        if n.parents.is_empty() && !self.roots.contains(&id) {
            let nn = n.n.clone();
            println!("removed {:?}, {:?}", id, nn);
            self.nodes.remove(&id);
            self.memo.remove(&nn);
            nn.for_each(|c| {
                self.remove_parent_from_child(id, c);
                self.may_remove(c)
            });
        }
    }

    fn remove_parent_from_child(&mut self, parent: Id, child: Id) {
        let parents = &mut self.nodes.get_mut(&child).unwrap().parents;
        print!("removing parent {:?} of {:?}, {:?}", parent, child, parents);
        let index = parents.iter().position(|x| *x == parent).unwrap();
        parents.remove(index);
        println!("--> {:?}", parents);

    }

    fn merge_upwards(&mut self, mut pending: Vec<Id>) -> HashMap<Id, Id> {
        // TODO: maybe the code can be simplified
        // step 1. is only necessary for parents of canonicalized nodes
        // step 2. is only necessary for nodes requiring canonicalization 
        let mut canonicalized = HashMap::default();

        while let Some(id) = pending.pop() {
            println!("{:?}", id);
            let mut node = self.nodes.remove(&id).unwrap();
            println!("merge {:?} / {:?} upwards", id, node);

            // 1. update node children
            let mut changed = false;
            let node_bak = node.n.clone();
            node.n.for_each_mut(|c| {
                if let Some(c2) = canonicalized.get(c) {
                    changed = true;
                    *c = *c2;
                }
            });
            if changed {
                println!("changed");
                assert!(self.memo.remove(&node_bak) == Some(id));
                self.memo.insert(node.n.clone(), id);
            }

            // 2. update node parents
            for p in &node.parents {
                let pnode = self[*p].clone();
                let pmemo = self.memo[&pnode];

                if *p != pmemo {
                    canonicalized.insert(*p, pmemo);

                    let pnode = self.nodes.get_mut(p).unwrap();
                    let pnode_parents = std::mem::replace(&mut pnode.parents, Vec::new());
                    pending.extend(pnode_parents.iter());
                    self.nodes.get_mut(&pmemo).unwrap().parents.extend(pnode_parents.iter());
                }
            }
            
            println!("--> {:?}", node);
            assert!(self.nodes.insert(id, node).is_none());
        }

        println!("canonicalized {:?}", canonicalized);
        for (id, _) in &canonicalized {
            let node = self.nodes.remove(id).unwrap();
            node.n.for_each(|c| self.remove_parent_from_child(*id, c));
        }

        canonicalized
    }

    fn check(&self) -> bool {
        self.check_memo() && self.check_parents()
    }

    fn check_memo(&self) -> bool {
        println!("{:?}", self);
        assert!(self.nodes.len() == self.memo.len());

        for (id, node) in &self.nodes {
            assert!(self.memo.get(&node.n) == Some(id));
        }

        true
    }

    fn check_parents(&self) -> bool {
        let mut parents = HashMap::default();

        for (&id, node) in &self.nodes {
            node.n.for_each(|child| {
                let v = parents.entry(child).or_insert_with(|| Vec::new());
                v.push(id);
            });
        }

        for (&id, node) in &self.nodes {
            let v = parents.entry(id).or_insert_with(|| Vec::new());
            v.sort();
            let mut v2 = node.parents.clone();
            v2.sort();
            assert_eq!(v, &mut v2);
        }

        true
    }

    pub fn as_dfg(&self) -> RecExpr<L> {
        let mut topo = Vec::with_capacity(self.nodes().len());
        let mut visited = HashSet::default();
        let mut to_topo = HashMap::default();
        // with_capacity(self.nodes().len());

        fn visit<L: Language>(
            id: &Id,
            topo: &mut Vec<L>,
            visited: &mut HashSet<Id>,
            to_topo: &mut HashMap<Id, Id>,
            g: &Graph<L>,
        ) {
            if !visited.contains(id) {
                visited.insert(*id);

                let node = &g[*id];
                let node2 = node.clone().map_children(|c| {
                    visit(&c, topo, visited, to_topo, g);
                    *to_topo.get(&c).unwrap()
                });
                to_topo.insert(*id, Id::from(topo.len()));
                topo.push(node2);
            }
        }

        for (id, _) in self.nodes() {
            visit(id, &mut topo, &mut visited, &mut to_topo, self);
        }

        assert!(topo.len() == self.nodes.len());
        RecExpr::from(topo)
    }

    pub fn as_egraph(&self) -> EGraph<L, ()> {
        let dfg = self.as_dfg();
        let topo = dfg.as_ref();

        let mut eg = EGraph::default();
        let mut ids = Vec::with_capacity(topo.len());
        for n in topo {
            let enode = n.clone().map_children(|c| ids[usize::from(c)]);
            ids.push(eg.add(enode));
        }

        assert!(eg.number_of_classes() == self.nodes.len());
        eg
    }
}

impl<L: Language + std::fmt::Display> Graph<L> {
    pub fn to_svg(&self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        self.as_egraph().dot().to_svg(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use SymbolLang as S;

    #[test]
    fn simple() {
        let mut g = Graph::default();
        let x = g.add(S::leaf("x"));
        let x2 = g.add(S::leaf("x"));
        let p = g.add(S::new("+", vec![x, x2]));

        g.add_root(p);

        println!("{:?}", g);

        assert!(x == Id::from(0));
        assert!(x2 == x);
        assert!(p == Id::from(1));

        assert!(g.memo.get(&S::leaf("x")) == Some(&Id::from(0)));
        assert!(g.memo.get(&S::new("+", vec![x, x2])) == Some(&Id::from(1)));
        assert!(g.memo.len() == 2);
        
        assert!(&g[x] == &S::leaf("x"));
        assert!(&g[p] == &S::new("+", vec![x, x2]));
        assert!(g.nodes.len() == 2);

        assert!(g.roots.len() == 1);
        assert!(g.roots[0] == p);

        let replacement = "(* ?x 2)".parse::<Pattern<S>>().unwrap().ast;
        let mut subst = Subst::default();
        subst.insert("?x".parse::<Var>().unwrap(), x);

        println!("{:?}", replacement);
        println!("{:?}", subst);

        g.replace(p, &replacement, &subst);
        
        println!("{:?}", g);

        assert!(g.memo.get(&S::new("+", vec![x, x2])) == None);
        assert!(g.memo.len() == 3);
        assert!(g.nodes.len() == 3);

        let c2 = g.add(S::leaf("2"));
        let m = g.add(S::new("*", vec![x, c2]));

        assert!(g.roots.len() == 1);
        assert!(g.roots[0] == m);
    }

    #[test]
    fn hashconsed() {
        let dfg = "(and (- (+ a 0)) (- a))".parse::<RecExpr<S>>().unwrap();
        let roots = vec![Id::from(dfg.as_ref().len() - 1)];
        let mut g = Graph::from_dfg(&dfg, roots);

        println!("{:?}", g);
        // g.to_svg("/tmp/g1.svg").unwrap();

        let lhs = "(+ ?x 0)".parse::<Pattern<S>>().unwrap();
        let rhs = "?x".parse::<Pattern<S>>().unwrap();

        let (id, subst) = lhs.search_graph(&g).unwrap();
        println!("{:?}: {:?}", id, subst);

        println!("replace");
        g.replace(id, &rhs.ast, &subst);

        println!("{:?}", g);
        // g.to_svg("/tmp/g2.svg").unwrap();
        assert!(g.nodes().len() == 3);
    }

    #[test]
    fn triple_add0() {
        for expr in ["(+ (+ (+ a 0) 0) 0)", "(+ (+ a 0) (+ 0 0))"] {
            let dfg = expr.parse::<RecExpr<S>>().unwrap();
            let roots = vec![Id::from(dfg.as_ref().len() - 1)];
            let mut g = Graph::from_dfg(&dfg, roots);
    
            println!("{:?}", g);
            // g.to_svg("/tmp/g0.svg").unwrap();
    
            let lhs = "(+ ?x 0)".parse::<Pattern<S>>().unwrap();
            let rhs = "?x".parse::<Pattern<S>>().unwrap();
    
            let mut counter = 0;
            while let Some((id, subst)) = lhs.search_graph(&g) {
                println!("{:?}: {:?}", id, subst);
                g.replace(id, &rhs.ast, &subst);
                counter += 1;
                // g.to_svg(format!("/tmp/g{}.svg", counter)).unwrap();
            }
    
            assert!(counter == 3);
            println!("{:?}", g);
            assert!(g.nodes().len() == 1);
            assert!(g.roots == g.nodes().map(|(&id, _)| id).collect::<Vec<_>>());
        }
    }

    #[test]
    fn lookup_rule() {
        let dfg = "(+ 1 2)".parse::<RecExpr<S>>().unwrap();
        let roots = vec![Id::from(dfg.as_ref().len() - 1)];
        let mut g = Graph::from_dfg(&dfg, roots);

        let lhs = "(+ 1 2)".parse::<Pattern<S>>().unwrap();
        let rhs = "3".parse::<Pattern<S>>().unwrap();

        let (id, subst) = lhs.search_graph(&g).unwrap();
        g.replace(id, &rhs.ast, &subst);

        assert!(g.nodes().len() == 1);
        assert!(g.roots == g.nodes().map(|(&id, _)| id).collect::<Vec<_>>());
    }
}