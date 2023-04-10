use crate::*;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::collections::BTreeSet;

/// A cost function to be used by a [`DagExtractor`].
///
/// `Cost` and its operations must define an ordered commutative monoid.
pub trait DagCostFunction<L: Language> {
    type Cost: PartialOrd + Debug + Clone + std::ops::AddAssign;

    /// Returns the zero of Cost.
    fn zero(&mut self) -> Self::Cost;

    /// Returns the cost of the given e-node.
    ///
    /// This cost should not depend on the e-node children.
    fn node_cost(&mut self, enode: &L) -> Self::Cost;
}

impl<L: Language> DagCostFunction<L> for AstSize {
    type Cost = usize;

    fn zero(&mut self) -> Self::Cost { 0 }
    fn node_cost(&mut self,  _enode: &L) -> Self::Cost { 1 }
}

#[derive(Debug)]
pub struct DagExtractor<'a, L: Language, A: Analysis<L>, CF> {
    cost_f: CF,
    // for each eclass,
    //  for each possible set of dependencies,
    //    there exists a best enode, minimizing cost
    bests: HashMap<Id, HashMap<BTreeSet<Id>, L>>,
    egraph: &'a EGraph<L, A>,
    // TODO: may be able to reduce complexity with immutable sharing of sets
}

impl<'a, L, A, CF> DagExtractor<'a, L, A, CF>
    where L: Language, A: Analysis<L>, CF: DagCostFunction<L>,
          L: 'a, A: 'a, CF::Cost: 'a
{
  fn new(egraph: &'a EGraph<L, A>, cost_f: CF) -> Self {
    let bests = HashMap::default();
    let mut extractor = DagExtractor {
        cost_f,
        bests,
        egraph
    };
    extractor.find_costs();

    extractor
  }

  // returns true if parents need to be updated
  fn update_bests(
    cost_f: &mut CF,
    bests: &mut HashMap<Id, HashMap<BTreeSet<Id>, L>>,
    u_id: Id,
    u_node: &L,
    dependencies: BTreeSet<Id>,
  ) -> bool {
    use hashbrown::hash_map::Entry;

    // TODO: what if there exists dependency subset/superset in map? collapse?
    let deps_to_best = bests.entry(u_id)
        .or_insert_with(|| HashMap::default());
    match deps_to_best.entry(dependencies) {
        Entry::Vacant(vac) => {
            vac.insert(u_node.clone());
            true // parents need to account for new dependencies
        }
        Entry::Occupied(mut occ) => {
            let occ_cost = cost_f.node_cost(occ.get());
            let new_cost = cost_f.node_cost(u_node);
            if new_cost < occ_cost {
                occ.insert(u_node.clone());
            }
            false // parents already accounted for these dependencies
        }
    }
  }

  fn find_costs(&mut self) {
    assert!(self.egraph.clean);

    // works with queue but IndexSet is stack
    let mut analysis_pending = HashSetQueuePop::<(L, Id)>::new();
    
    // start from leaves
    for eclass in self.egraph.classes() {
        debug_assert!(self.egraph.find(eclass.id) == eclass.id);
        for enode in &eclass.nodes {
            debug_assert!(enode.all(|c| self.egraph.find(c) == c));

            if enode.is_leaf() {
                // let node_cost = self.cost_f.node_cost(self.egraph, eclass.id, &enode);
                let dependencies = BTreeSet::default();
                if Self::update_bests(&mut self.cost_f, &mut self.bests, eclass.id, enode, dependencies) {
                    Self::analyse_parents_next(&mut analysis_pending, self.egraph, eclass);
                }
            }
        }
    }
    
    // work towards parents
    while let Some((enode, eclass_id)) = analysis_pending.pop() {
        debug_assert!(!enode.is_leaf());
        debug_assert!(self.egraph.find(eclass_id) == eclass_id);
        debug_assert!(enode.all(|c| self.egraph.find(c) == c));

        if enode.all(|c| self.bests.contains_key(&c)) {
            let eclass = &self.egraph[eclass_id];
            // let node_cost = self.cost_f.node_cost(self.egraph, u_id, u_node);

            let mut dependencies = vec![];
            let children = enode.children();
            Self::collect_dependencies(&mut dependencies, &self.bests, children, children.iter().cloned().collect());

            let mut needs_update = false;
            for d in dependencies {
                if Self::update_bests(&mut self.cost_f, &mut self.bests, eclass.id, &enode, d) {
                    needs_update = true;
                }
            }
            if needs_update {
                Self::analyse_parents_next(&mut analysis_pending, &self.egraph, eclass);
            }
        } else {
            analysis_pending.insert((enode, eclass_id));
        }
    }
  }

  fn collect_dependencies(
    dependencies: &mut Vec<BTreeSet<Id>>,
    bests: &HashMap<Id, HashMap<BTreeSet<Id>, L>>,
    remaining_children: &[Id],
    dependencies_so_far: BTreeSet<Id>,
  ) {
    match remaining_children.split_first() {
        None => {
            dependencies.push(dependencies_so_far);
        }
        Some ((child, remaining)) => {
            // TODO: optimize this loop 
            // + avoid redundant entries between children?
            for (child_dependencies, _) in &bests[child] {
                Self::collect_dependencies(
                    dependencies, bests,
                    remaining,
                    &dependencies_so_far | child_dependencies,
                )
            }
        }
    }
  }

  fn analyse_parents_next(
    analysis_pending: &mut HashSetQueuePop::<(L, Id)>,
    egraph: &EGraph<L, A>,
    eclass: &EClass<L, A::Data>,
  ) {
    analysis_pending.extend(eclass.parents.iter().map(|(n, id)| {
        let u_n = n.clone().map_children(|id| egraph.find(id));
        let u_id = egraph.find(*id);
        (u_n, u_id)
    }));
  }

  fn find_best(&mut self, eclasses: &[Id]) -> (CF::Cost, RecExpr<L>, Vec<Id>) {
    let mut dependencies = vec![];
    Self::collect_dependencies(&mut dependencies, &self.bests, eclasses, eclasses.iter().cloned().collect());

    let mut solutions = vec![];
    for d in &dependencies {
        solutions.push(self.find_best_with_dependencies(d));
    }
    match solutions.into_iter().min_by(|(ca, _, _), (cb, _, _)| ca.partial_cmp(cb).unwrap()) {
        None => panic!(""),
        Some((cost, expr, to_expr)) => (cost, expr, eclasses.iter().map(|id| to_expr[id]).collect())
    }
  }

  fn find_best_with_dependencies(&mut self, dependencies: &BTreeSet<Id>) -> (CF::Cost, RecExpr<L>, HashMap<Id, Id>) {
    let mut cost = self.cost_f.zero();
    let mut expr = RecExpr::default();
    let mut to_expr = HashMap::<Id, Id>::default();
    while to_expr.len() < dependencies.len() {
        let mut changed = false;
        for d in dependencies {
            if !to_expr.contains_key(d) {
                let available_nodes_with_cost = self.egraph[*d].nodes.iter()
                    .filter(|n| n.all(|id| dependencies.contains(&id)))
                    .map(|n| (self.cost_f.node_cost(n), n))
                    .collect::<Vec<_>>();
                match available_nodes_with_cost.iter().min_by(|(ca, _), (cb, _)| ca.partial_cmp(cb).unwrap()).map(|(c, _)| c).cloned() {
                    None => {}
                    Some(best_cost) => {
                        let constructible_best_node = available_nodes_with_cost.into_iter()
                            .filter(|(c, n)| c == &best_cost && n.all(|id| to_expr.contains_key(&id)))
                            .next();
                        if let Some((_, best_node)) = constructible_best_node {
                            cost += best_cost.clone();
                            let new_id = expr.add(best_node.clone().map_children(|id| to_expr[&id]));
                            to_expr.insert(*d, new_id);
                            changed = true;
                        }
                    }
                }
            }
        }
        assert!(changed);
    }
    (cost, expr, to_expr)
  }
}


/// --- egg-sketches analysis.rs

pub struct HashSetQueuePop<T> {
    map: HashSet<T>,
    queue: std::collections::VecDeque<T>,
}

impl<T: Eq + std::hash::Hash + Clone> HashSetQueuePop<T> {
    pub fn new() -> Self {
        HashSetQueuePop {
            map: HashSet::default(),
            queue: std::collections::VecDeque::new(),
        }
    }

    pub fn insert(&mut self, t: T) {
        if self.map.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for t in iter.into_iter() {
            self.insert(t);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let res = self.queue.pop_front();
        res.as_ref().map(|t| self.map.remove(t));
        res
    }
}

#[cfg(test)]
mod tests {
    use crate::{SymbolLang as S, *};
    use super::*;

    #[test]
    fn simple_dag_extract() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));
        egraph.rebuild();

        let mut ext = DagExtractor::new(&egraph, AstSize);
        for (k, v) in &ext.bests {
            println!("e-class {:?}: {:?}", k, v);
        }

        let (cost, expr, ids) = ext.find_best(&[f, g]);
        println!("best cost: {:?}", cost);
        println!("best expr: {:?}", expr);
        println!("root ids: {:?}", ids);
        assert_eq!(expr.as_ref().len(), 4);
        assert_eq!(ids.len(), 2);

        panic!("WIP");
    }

    // example from issue #207
    #[test]
    fn dag_extract_207() {
        let mut egraph = EGraph::<SymbolLang, ()>::default();

        let g = egraph.add_expr(&"(g v x)".parse().unwrap());
        let v = egraph.add_expr(&"v".parse().unwrap());
        let f = egraph.add(SymbolLang::new("f", vec![v, g]));
        let top = egraph.add(SymbolLang::new("list", vec![f, g]));
        egraph.rebuild();

        let runner = Runner::default()
            .with_iter_limit(100)
            .with_node_limit(10_000)
            .with_egraph(egraph)
            .run(&vec![rewrite!("f"; "(f ?v (g ?v ?a))" => "?a")]);
        // runner.egraph.dot().to_dot("tmp.dot").unwrap();

        let (cost, expr, ids) = DagExtractor::new(&runner.egraph, AstSize).find_best(&[top]);
        // println!("{:?}", result);
        assert_eq!(cost, 4);
        assert_eq!(expr.as_ref().len(), 4);
        // TODO: check expr is list x (g v x)
        assert_eq!(ids, vec![3]);
    }

    #[test]
    fn dag_extract_207_bis() {
        struct CostFn;

        impl DagCostFunction<SymbolLang> for CostFn {
            type Cost = f64;
        
            fn zero(&mut self) -> Self::Cost { 0.0 }
            fn node_cost(&mut self, enode: &SymbolLang) -> Self::Cost {
                match enode.op.as_str() {
                    "A" => 1.0,
                    "B" => 2.0,
                    "x" => 10.0,
                    "y" => 3.0,
                    _ => 0.1,
                }
            }
        }

        let mut egraph = EGraph::<SymbolLang, ()>::default();

        let a = egraph.add_expr(&"(A y)".parse().unwrap());
        let x = egraph.add_expr(&"x".parse().unwrap());
        let y = egraph.add_expr(&"y".parse().unwrap());
        let top = egraph.add(SymbolLang::new("list", vec![a, y]));
        egraph.union(a, x);
        egraph.rebuild();
        egraph.dot().to_dot("tmp1.dot").unwrap();
        // correcly finds (list (A y) y); instead of (list x y) from issue
        println!("{:?}", DagExtractor::new(&egraph, CostFn).find_best(&[top]));

        let b = egraph.add_expr(&"(B x)".parse().unwrap());
        egraph.union(b, y);
        egraph.rebuild();
        egraph.dot().to_dot("tmp2.dot").unwrap();
        println!("{:?}", DagExtractor::new(&egraph, CostFn).find_best(&[top])); // issue: (list x (B x)) while (list (A y) y) is optimal ?

        panic!("");
    }
}
