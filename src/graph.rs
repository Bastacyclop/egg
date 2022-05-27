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
        self.add_internal(node, |_, _| true)
    }

    fn add_internal<PF>(&mut self, node: L, mut push_parent: PF) -> Id 
        where PF: FnMut(Id, Id) -> bool
    {
        if let Some(existing_id) = self.lookup(&node) {
            existing_id
        } else {
            let id = self.next_id();
            assert!(self.nodes.insert(id, Node {
                n: node.clone(), parents: Vec::new(),
            }).is_none());
            assert!(self.memo.insert(node.clone(), id).is_none());

            node.for_each(|c| {
                if push_parent(c, id) {
                    let parents = &mut self.nodes.get_mut(&c)
                        .unwrap_or_else(|| panic!("Invalid child id"))
                        .parents;
                    parents.push(id);
                    // TODO: dedup?
                }
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
        // 0. create original backup for replacement
        let original_backup = self.next_id();
        let mut original_backup_parents = Vec::new();

        // 1. create replacement
        let ast = ast.as_ref();
        let mut ids = vec![0.into(); ast.len()];
        for (i, pat_node) in ast.iter().enumerate() {
            let id = match pat_node {
                ENodeOrVar::Var(w) => subst[*w],
                ENodeOrVar::ENode(e) => {
                    let n = e.clone().map_children(|c| ids[usize::from(c)]);
                    self.add_internal(n, |child, id| {
                        let is_dummy = child == original;
                        if is_dummy { 
                            original_backup_parents.push(id);
                        }
                        !is_dummy
                    })
                }
            };
            let id = if id == original { original_backup } else { id };
            ids[i] = id;
        }
        let replacement = *ids.last().unwrap();

        if original_backup == replacement {
            println!("WARNING: weird rule?");
            return
        }

        // 2. link original parents to replacement
        let ori_n = self.nodes.remove(&original)
            .unwrap_or_else(|| panic!("Invalid id"));
        self.move_parents(&ori_n.parents[..], original, replacement);

        // 3. link original backup parents to original
        self.move_parents(&original_backup_parents[..], original_backup, original);
        assert!(self.nodes.insert(original, Node {
            n: ori_n.n, parents: original_backup_parents
        }).is_none());

        // 4. collect garbage
        self.may_remove(original);
    }

    fn move_parents(&mut self, parents: &[Id], of: Id, to: Id) {
        for &p in parents {
            let n = &mut self.nodes.get_mut(&p).unwrap().n;
            assert!(self.memo.remove(n) == Some(p));
            n.for_each_mut(|pc| {
                if *pc == of { *pc = to }
            });
            self.memo.insert(n.clone(), p);
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
            self.nodes.remove(&id);
            self.memo.remove(&nn);
            nn.for_each(|c| {
                let cps = &mut self.nodes.get_mut(&c).unwrap().parents;
                let index = cps.iter().position(|x| *x == id).unwrap();
                cps.remove(index);
                self.may_remove(c)
            });
        }
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

        let lhs = "(+ ?x 0)".parse::<Pattern<S>>().unwrap();
        let rhs = "?x".parse::<Pattern<S>>().unwrap();

        let (id, subst) = lhs.search_graph(&g).unwrap();
        println!("{:?}: {:?}", id, subst);

        println!("replace");
        g.replace(id, &rhs.ast, &subst);

        println!("{:?}", g);
        assert!(g.nodes().len() == 3);
    }
}

// TODO: a --> a + 0 [a + 0 --> (a + 0) + 0]