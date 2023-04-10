use crate::*;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::collections::BTreeSet;

/// A cost function to be used by a [`DagExtractor`].
pub trait DagCostFunction<L: Language> {
    type Cost: PartialOrd + Debug + Clone;

    /// Returns the cost of the given e-node.
    ///
    /// This cost should not depend on the e-node children.
    fn node_cost(&mut self, enode: &L) -> Self::Cost;
}

impl<L: Language> DagCostFunction<L> for AstSize {
    type Cost = usize;

    fn node_cost(&mut self,  _enode: &L) -> Self::Cost {
        1
    }
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
            Self::collect_dependencies(&mut dependencies, &self.bests, eclass, &enode, &mut analysis_pending, children, children.iter().cloned().collect());

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
    eclass: &EClass<L, A::Data>,
    enode: &L,
    analysis_pending: &mut HashSetQueuePop::<(L, Id)>,
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
                    dependencies, bests, eclass, enode, analysis_pending,
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
        for (k, v) in ext.bests {
            println!("e-class {:?}: {:?}", k, v);
        }
        panic!("WIP");

        /*
        let mut ext = LpExtractor::new(&egraph, AstSize);
        ext.timeout(10.0); // way too much time
        let (exp, ids) = ext.solve_multiple(&[f, g]);
        println!("{:?}", exp);
        println!("{}", exp);
        assert_eq!(exp.as_ref().len(), 4);
        assert_eq!(ids.len(), 2);
        */
    }
}
