use crate::*;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::collections::{BTreeSet, BinaryHeap};

/// A cost function to be used by a [`DagExtractor`].
///
/// `Cost` and its operations must define an ordered commutative monoid.
pub trait DagCostFunction<L: Language> {
    type Cost: PartialOrd + Debug + Clone + std::ops::Add<Output=Self::Cost> + std::ops::AddAssign + PartialEq;

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

type Visited = BTreeSet<Id>;
type ToVisit = BTreeSet<Id>;
type SolutionNode = (Visited, ToVisit);

struct State<Cost> {
    cost: Cost,
    solution_node: SolutionNode,
}

// Manually implement Ord so we get a min-heap instead of a max-heap
// + Allow PartialOrd
impl<Cost> Ord for State<Cost> where Cost: PartialOrd {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<Cost> PartialOrd for State<Cost> where Cost: PartialOrd {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        other.cost.partial_cmp(&self.cost)
    }
}

impl<Cost> PartialEq for State<Cost> where Cost: PartialEq {
    fn eq(&self, other: &Self) -> bool {
        other.cost.eq(&self.cost)
    }
}

// TODO: what is this implying?
impl<Cost> Eq for State<Cost> where Cost: PartialEq {}

#[derive(Debug)]
pub struct DagExtractor<'a, L: Language, A: Analysis<L>, CF> {
    cost_f: CF,
    // for each eclass,
    //  for each possible set of dependencies,
    //    there exists a best enode, minimizing cost
    // bests: HashMap<SolutionNode, CF::Cost>,
    egraph: &'a EGraph<L, A>,
    // TODO: may be able to reduce complexity with immutable sharing of sets
}

impl<'a, L, A, CF> DagExtractor<'a, L, A, CF>
    where L: Language, A: Analysis<L>, CF: DagCostFunction<L>,
          L: 'a, A: 'a, CF::Cost: 'a
{
  pub fn new(egraph: &'a EGraph<L, A>, cost_f: CF) -> Self {
    // let bests = HashMap::default();
    let mut extractor = DagExtractor {
        cost_f,
        // bests,
        egraph
    };
    // extractor.find_costs();
    /* DEBUG:
    for (k, v) in &extractor.bests {
        println!("e-class {:?}: {:?}", k, v);
    } */

    extractor
  }

  pub fn find_best(&mut self, roots: &[Id]) -> (CF::Cost, RecExpr<L>, Vec<Id>) {
    // TODO: id for solution nodes
    let mut bests = HashMap::<SolutionNode, (CF::Cost, Vec<L>, SolutionNode)>::default();

    let mut heap = BinaryHeap::new();
    // TODO: avoid duplication of sets
    heap.push(State {
        cost: self.cost_f.zero(),
        solution_node: (
            Visited::default(),
            roots.iter().map(|&id| self.egraph.find(id)).collect()
        ),
    });

    while let Some(State { cost, solution_node }) = heap.pop() {
        println!("fb: {:?}, {:?}", cost, solution_node);
        // let (visited, to_visit) = solution_node;
        // We found a solution, we can stop here.
        if solution_node.1.is_empty() {
            return Self::build_solution(cost, solution_node.0, &bests, &self.egraph, roots);
        }

        // This path is suboptimal.
        if (!solution_node.0.is_empty()) && cost > bests[&solution_node].0 {
            println!("suboptimal");
            continue;
        }
        // TODO: what if = best?

        let n_visited = &solution_node.0 | &solution_node.1;
        for (n_cost, n_to_visit, n_nodes) in Self::next_moves(cost, solution_node.1.clone(), &self.egraph, &mut self.cost_f) {
            println!("next move: {:?}, {:?}, {:?}",
                n_cost, n_to_visit, n_nodes);
            // This is a cycle.
            if !n_visited.is_disjoint(&n_to_visit) {
                println!("cycle");
                continue;
            }

            let next = State {
                cost: n_cost,
                solution_node: (n_visited.clone(), n_to_visit),
                // &n_to_visit - &n_visited = n_to_visit
            };
            if bests.get(&next.solution_node).map(|sn| next.cost < sn.0).unwrap_or(true) {
                println!("push");
                bests.insert(next.solution_node.clone(), (next.cost.clone(), n_nodes, solution_node.clone()));
                heap.push(next);
            }
        }
    }

    panic!("extraction failed");
  }

  fn next_moves(
    cost: CF::Cost,
    to_visit: ToVisit,
    egraph: &EGraph<L, A>,
    cost_f: &mut CF,
  ) -> Vec<(CF::Cost, ToVisit, Vec<L>)>
  {
    let mut result = Vec::new();
    let remaining: Vec<Id> = to_visit.into_iter().collect();
    let mut nodes_so_far = Vec::new();
    Self::next_moves_rec(&remaining[..], egraph, cost_f, cost, &mut nodes_so_far, ToVisit::default(), &mut result);
    result
  }

  fn next_moves_rec(
    remaining: &[Id],
    egraph: &EGraph<L, A>,
    cost_f: &mut CF,
    cost_so_far: CF::Cost,
    nodes_so_far: &mut Vec<L>,
    n_to_visit_so_far: ToVisit,
    acc: &mut Vec<(CF::Cost, ToVisit, Vec<L>)>,
  )
  {
    match remaining.split_first() {
        None => acc.push((cost_so_far, n_to_visit_so_far, nodes_so_far.clone())),
        Some((&tv, rem)) => {
            let eclass_to_visit = &egraph[tv];
            for possible_enode in &eclass_to_visit.nodes {
                debug_assert!(possible_enode.all(|c| egraph.find(c) == c));
        
                let cost_so_far = cost_so_far.clone() + cost_f.node_cost(possible_enode);
                nodes_so_far.push(possible_enode.clone());
                let children: BTreeSet<_> = possible_enode.children().iter().cloned().collect();
                let n_to_visit_so_far = &n_to_visit_so_far | &children;
                Self::next_moves_rec(rem, egraph, cost_f, cost_so_far, nodes_so_far, n_to_visit_so_far, acc);
                nodes_so_far.pop();
            }
        }
    }
  }

  fn build_solution(
    cost: CF::Cost,
    visited: Visited,
    bests: &HashMap<SolutionNode, (CF::Cost, Vec<L>, SolutionNode)>,
    egraph: &EGraph<L, A>,
    roots: &[Id],
  ) -> (CF::Cost, RecExpr<L>, Vec<Id>) {
    println!("visited: {:?}", visited);
    println!("bs: {:?}", bests);
    // {0, 1, 3}, {}: 3.1 [B 1, A 0], {3}, {0, 1}
    // {3}, {0, 1}: 0.1 [list 1 0], {}, {3}
    let solution_node = &(visited, ToVisit::default());
    debug_assert!(cost == bests[solution_node].0);
    let mut expr = RecExpr::default();
    let mut to_expr = HashMap::default();
    Self::build_solution_rec(
        solution_node,
        bests,
        egraph,
        &mut expr,
        &mut to_expr
    );
    (cost, expr, roots.iter().map(|r| to_expr[r]).collect())
  }

  fn build_solution_rec(
    solution_node: &SolutionNode,
    bests: &HashMap<SolutionNode, (CF::Cost, Vec<L>, SolutionNode)>,
    egraph: &EGraph<L, A>,
    expr: &mut RecExpr<L>,
    to_expr: &mut HashMap<Id, Id>,
  )
  {
    println!("bsr");
    match bests.get(solution_node) {
        None => (),
        Some((_, nodes, prev_solution_node)) => {
            for n in nodes {
                println!("to_expr: {:?}", to_expr);
                println!("n: {:?}", n);
                let new_id = expr.add(n.clone().map_children(|id| to_expr[&id]));
                to_expr.insert(egraph.lookup(n.clone()).unwrap(), new_id);
            }
            Self::build_solution_rec(
                prev_solution_node,
                bests,
                egraph, 
                expr,
                to_expr
            );
        }
    }
  }

/*
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

    println!("LEAVES OK");
    
    // work towards parents
    while let Some((enode, eclass_id)) = analysis_pending.pop() {
        println!("PROCESSING: {:?}, {:?}", enode, eclass_id);

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

  pub fn find_best(&mut self, eclasses: &[Id]) -> (CF::Cost, RecExpr<L>, Vec<Id>) {
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
    let egraph = &self.egraph;
    let cost_f = &mut self.cost_f;

    let mut cost = cost_f.zero();
    let mut expr = RecExpr::default();
    let mut to_expr = HashMap::<Id, Id>::default();
    while to_expr.len() < dependencies.len() {
        let mut changed = false;
        for d in dependencies {
            if !to_expr.contains_key(d) {
                let available_nodes_with_cost = egraph[*d].nodes.iter()
                    .filter(|n| n.all(|id| dependencies.contains(&id)))
                    .map(|n| (cost_f.node_cost(n), n))
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
        // TODO: maybe this logic can be simplified
        if !changed {
            // constructing a best node requires constructing other nodes that are not best:
            // - make progress greedily with the globally cheapest constructible node
            let constructible_best_node = dependencies.iter()
                .filter(|d| !to_expr.contains_key(d))
                .flat_map(|d| {
                    egraph[*d].nodes.iter()
                        .filter(|n| n.all(|id| to_expr.contains_key(&id)))
                        .map(move |n| (*d, n.clone()))
                })
                .map(|(d, n)| (d, cost_f.node_cost(&n), n))
                .min_by(|(_, ca, _), (_, cb, _)| ca.partial_cmp(cb).unwrap());
            match constructible_best_node {
                None => panic!("find_best is stuck at: {:?}", expr),
                Some((best_d, best_cost, best_node)) => {
                    cost += best_cost;
                    let new_id = expr.add(best_node.map_children(|id| to_expr[&id]));
                    to_expr.insert(best_d, new_id);
                }
            }
        }
    }
    (cost, expr, to_expr)
  }
  */
}


/// --- egg-sketches analysis.rs

pub(crate) struct HashSetQueuePop<T> {
    map: HashSet<T>,
    queue: std::collections::VecDeque<T>,
}

impl<T: Eq + std::hash::Hash + Clone> HashSetQueuePop<T> {
    pub(crate) fn new() -> Self {
        HashSetQueuePop {
            map: HashSet::default(),
            queue: std::collections::VecDeque::new(),
        }
    }

    pub(crate) fn insert(&mut self, t: T) {
        if self.map.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub(crate) fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for t in iter.into_iter() {
            self.insert(t);
        }
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
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
        crate::init_logger();

        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));
        egraph.rebuild();

        let mut ext = DagExtractor::new(&egraph, AstSize);
        let (cost, expr, ids) = ext.find_best(&[f, g]);
        println!("best cost: {:?}", cost);
        println!("best expr: {:?}", expr);
        println!("root ids: {:?}", ids);
        assert_eq!(cost, 4);
        assert_eq!(expr.as_ref().len(), 4);
        assert_eq!(ids.len(), 2);
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
        assert_eq!(ids, vec![Id::from(3)]);
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
        // egraph.dot().to_dot("tmp1.dot").unwrap();
        // correcly finds (list (A y) y); instead of (list x y) from issue
        let (cost1, expr1, ids1) = DagExtractor::new(&egraph, CostFn).find_best(&[top]);
        assert_eq!(cost1, 4.1);
        assert_eq!(expr1.as_ref().len(), 3);
        assert_eq!(ids1, vec![Id::from(2)]);

        let b = egraph.add_expr(&"(B x)".parse().unwrap());
        egraph.union(b, y);
        egraph.rebuild();
        // egraph.dot().to_dot("tmp2.dot").unwrap();
        // correctly finds (list (A y) y); instead of (list x (B x)) from issue
        let (cost2, expr2, ids2) = DagExtractor::new(&egraph, CostFn).find_best(&[top]); 
        assert_eq!(cost2, 4.1);
        assert_eq!(expr2.as_ref().len(), 3);
        assert_eq!(ids2, vec![Id::from(2)]);
    }
}
