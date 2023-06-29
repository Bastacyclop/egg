use coin_cbc::{Col, Model, Sense};

use crate::*;

/// A structure to perform extraction using integer linear programming.
/// This uses the [`cbc`](https://projects.coin-or.org/Cbc) solver.
/// You must have it installed on your machine to use this feature.
/// You can install it using:
///
/// | OS               | Command                                  |
/// |------------------|------------------------------------------|
/// | Fedora / Red Hat | `sudo dnf install coin-or-Cbc-devel`     |
/// | Ubuntu / Debian  | `sudo apt-get install coinor-libcbc-dev` |
/// | macOS            | `brew install cbc`                       |
///
/// On macOS, you might also need the following in your `.zshrc` file:
/// `export LIBRARY_PATH=$LIBRARY_PATH:$(brew --prefix)/lib`
///
/// # Example
/// ```
/// use egg::*;
/// let mut egraph = EGraph::<SymbolLang, ()>::default();
///
/// let f = egraph.add_expr(&"(f x x x)".parse().unwrap());
/// let g = egraph.add_expr(&"(g (g x))".parse().unwrap());
/// egraph.union(f, g);
/// egraph.rebuild();
///
/// let best = Extractor::new(&egraph, AstSize).find_best(f).1;
/// let lp_best = LpExtractor::new(&egraph, AstSize).solve(f);
///
/// // In regular extraction, cost is measures on the tree.
/// assert_eq!(best.to_string(), "(g (g x))");
///
/// // Using ILP only counts common sub-expressions once,
/// // so it can lead to a smaller DAG expression.
/// assert_eq!(lp_best.to_string(), "(f x x x)");
/// assert_eq!(lp_best.as_ref().len(), 2);
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
pub struct LpExtractor2<'a, L: Language, N: Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    model: Model,
    vars: HashMap<Id, ClassVars>,
}

struct ClassVars {
    active: Col,
    order: Col,
    nodes: Vec<Option<Col>>,
}

impl<'a, L, N> LpExtractor2<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Create an [`LpExtractor`] using costs from the given [`LpCostFunction`].
    /// See those docs for details.
    pub fn new<CF>(egraph: &'a EGraph<L, N>, mut cost_function: CF) -> Self
    where
        CF: LpCostFunction<L, N>,
    {
        let max_order = egraph.total_number_of_nodes() as f64 * 10.0;

        // FIXME: avoid evaluating cost function twice?
        let mut to_prune: HashSet<(Id, usize)> = Default::default();
        find_nodes_to_prune(egraph, |id, i| {
            to_prune.insert((id, i));
        }, &mut cost_function);
        // println!("to prune: {:?}", to_prune);

        let mut model = Model::default();
        let vars: HashMap<Id, ClassVars> = egraph
            .classes()
            .map(|class| {
                let cvars = ClassVars {
                    active: model.add_binary(),
                    order: model.add_col(),
                    nodes: class.nodes.iter().enumerate().map(|(i, _)| {
                        if to_prune.contains(&(class.id, i)) {
                          None
                        } else {
                          Some(model.add_binary())
                        }
                    }).collect(),
                };
                model.set_col_upper(cvars.order, max_order);
                (class.id, cvars)
            })
            .collect();

        for (&id, class) in &vars {
            // class active == some node active
            // sum(for node_active in class) == class_active
            let row = model.add_row();
            model.set_row_equal(row, 0.0);
            model.set_weight(row, class.active, -1.0);
            for &node_active in class.nodes.iter().flatten() {
                model.set_weight(row, node_active, 1.0);
            }

            for (node, &node_active_opt) in egraph[id].iter().zip(&class.nodes) {
                if let Some(node_active) = node_active_opt {
                    for child in node.children() {
                        let child_active = vars[child].active;
                        // node active implies child active, encoded as:
                        //   node_active <= child_active
                        //   node_active - child_active <= 0
                        let row = model.add_row();
                        model.set_row_upper(row, 0.0);
                        model.set_weight(row, node_active, 1.0);
                        model.set_weight(row, child_active, -1.0);
                    }
                }
            }
        }

        model.set_obj_sense(Sense::Minimize);
        for class in egraph.classes() {
            for (node, &node_active_opt) in class.iter().zip(&vars[&class.id].nodes) {
                if let Some(node_active) = node_active_opt {
                    model.set_obj_coeff(node_active, cost_function.node_cost(egraph, class.id, node));
                }
            }
        }

        dbg!(max_order);

        Self {
            egraph,
            model,
            vars,
        }
    }

    /// Set the cbc timeout in seconds.
    pub fn timeout(&mut self, seconds: f64) -> &mut Self {
        self.model.set_parameter("seconds", &seconds.to_string());
        self
    }

    /// Extract a single rooted term.
    ///
    /// This is just a shortcut for [`LpExtractor::solve_multiple`].
    pub fn solve(&mut self, root: Id) -> RecExpr<L> {
        self.solve_multiple(&[root]).0
    }

    /// Extract (potentially multiple) roots
    pub fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        let egraph = self.egraph;

        for class in self.vars.values() {
            self.model.set_binary(class.active);
        }

        for root in roots {
            let root = &egraph.find(*root);
            self.model.set_col_lower(self.vars[root].active, 1.0);
        }

        let solution = self.model.solve();
        log::info!(
            "CBC status {:?}, {:?}",
            solution.raw().status(),
            solution.raw().secondary_status()
        );

        let mut todo: Vec<Id> = roots.iter().map(|id| self.egraph.find(*id)).collect();
        let mut expr = RecExpr::default();
        // converts e-class ids to e-node ids
        let mut ids: HashMap<Id, Id> = HashMap::default();

        while let Some(&id) = todo.last() {
            if ids.contains_key(&id) {
                todo.pop();
                continue;
            }
            let v = &self.vars[&id];
            // println!("{:?}: {:?}", id, v.nodes.iter().map(|n_opt| n_opt.is_some()).collect::<Vec<_>>());
            assert!(solution.col(v.active) > 0.0);
            let node_idx = v.nodes.iter().position(|&n_opt|
                n_opt.map(|n| solution.col(n) > 0.0).unwrap_or(false)
            ).unwrap();
            let node = &self.egraph[id].nodes[node_idx];
            if node.all(|child| ids.contains_key(&child)) {
                let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
                ids.insert(id, new_id);
                todo.pop();
            } else {
                todo.extend_from_slice(node.children())
            }
        }

        let root_idxs = roots.iter().map(|root| *ids.get(&egraph.find(*root)).expect("LpExtract found no solution")).collect();

        assert!(expr.is_dag(), "LpExtract found a cyclic term!: {:?}", expr);
        (expr, root_idxs)
    }
}

/// pruned if infinite cost or creates a cycle
fn find_nodes_to_prune<L, N, CF>(egraph: &EGraph<L, N>, mut f: impl FnMut(Id, usize),cost_function: &mut CF)
where
    L: Language,
    N: Analysis<L>,
    CF: LpCostFunction<L, N>
{
    enum Color {
        White,
        Gray,
        Black,
    }
    type Enter = bool;

    let mut color: HashMap<Id, Color> = egraph.classes().map(|c| (c.id, Color::White)).collect();
    let mut stack: Vec<(Enter, Id)> = egraph.classes().map(|c| (true, c.id)).collect();

    while let Some((enter, id)) = stack.pop() {
        if enter {
            *color.get_mut(&id).unwrap() = Color::Gray;
            stack.push((false, id));
            for (i, node) in egraph[id].iter().enumerate() {
                if cost_function.node_cost(egraph, id, node) == std::f64::INFINITY {
                    f(id, i);
                    continue;
                }
                for child in node.children() {
                    match &color[child] {
                        Color::White => stack.push((true, *child)),
                        Color::Gray => f(id, i),
                        Color::Black => (),
                    }
                }
            }
        } else {
            *color.get_mut(&id).unwrap() = Color::Black;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{SymbolLang as S, *};

    #[test]
    fn simple_lp_extract_two() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));

        let mut ext = LpExtractor2::new(&egraph, AstSize);
        ext.timeout(10.0); // way too much time
        let (exp, ids) = ext.solve_multiple(&[f, g]);
        println!("{:?}", exp);
        println!("{}", exp);
        assert_eq!(exp.as_ref().len(), 4);
        assert_eq!(ids.len(), 2);
    }

    #[test]
    fn simple_lp_extract_inf() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));
        let b = egraph.add(S::leaf("b"));
        egraph.union(f, b);
        egraph.union(g, b);
        egraph.rebuild();

        struct OnlyLeaves;
        impl LpCostFunction<S, ()> for OnlyLeaves {
            fn node_cost(&mut self, _egraph: &EGraph<S, ()>, _eclass: Id, enode: &S) -> f64 {
                if enode.is_leaf() {
                    1.0
                } else {
                    std::f64::INFINITY
                }
            }
        }

        let mut ext = LpExtractor2::new(&egraph, OnlyLeaves);
        ext.timeout(10.0); // way too much time
        let (exp, ids) = ext.solve_multiple(&[f, g]);
        println!("{:?}", exp);
        println!("{}", exp);
        assert_eq!(exp.as_ref().len(), 1);
        assert_eq!(ids.len(), 2);
    }
}
