use std::collections::HashMap;

use slotted_egraphs::*;

define_language! {
    enum Type {
        Unit() = "1",
        Prod(AppliedId, AppliedId) = "*",
        Arr(AppliedId, AppliedId) = "→",
        List(AppliedId) = "list",
        Forall(Bind<AppliedId>) = "∀",
        Var(Slot) = "var",
        Symbol(Symbol)
    }
}

fn make_rules() -> Vec<Rewrite<Type, ()>> {
    vec![
        rw!("*-comm";                  "(* ?a ?b)" => "(* ?b ?a)"               ),
        rw!("*-idl";                    "(* 1 ?a)" => "?a"                      ),
        rw!("*-idr";                    "(* ?a 1)" => "?a"                      ),
        rw!("→-idl";                    "(→ 1 ?a)" => "?a"                      ),
        rw!("→-zeror";                  "(→ ?a 1)" => "1"                       ),
        rw!("→-swap";           "(→ ?a (→ ?b ?c))" => "(→ ?b (→ ?a ?c))"        ),
        rw!("*-assoc";          "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"        ),
        rw!("*-unassoc";        "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"        ),
        rw!("curry";            "(→ (* ?a ?b) ?c)" => "(→ ?a (→ ?b ?c))"        ),
        rw!("uncurry";          "(→ ?a (→ ?b ?c))" => "(→ (* ?a ?b) ?c)"        ),
        rw!("distrib";          "(→ ?a (* ?b ?c))" => "(* (→ ?a ?b) (→ ?a ?c))" ),
        rw!("undistrib"; "(* (→ ?a ?b) (→ ?a ?c))" => "(→ ?a (* ?b ?c))"        ),
        rw!("∀-swap";        "(∀ $1 (∀ $2 ?body))" => "(∀ $2 (∀ $1 ?body))"     ),
    ]
}

fn search(
    heystack: &HashMap<String, RecExpr<Type>>,
    needle: RecExpr<Type>,
) -> HashMap<String, (RecExpr<Type>, String)> {
    let mut egraph = EGraph::new(());

    let name_to_id: HashMap<String, (AppliedId, RecExpr<Type>)> = heystack
        .iter()
        .map(|(name, ty)| {
            let id = egraph.add_expr(ty.clone());
            (name.clone(), (id, ty.clone()))
        })
        .collect();

    let needle_id = egraph.add_expr(needle.clone());

    run_eqsat(&mut egraph, make_rules(), 30, 60, |_| Ok(()));

    name_to_id
        .into_iter()
        .filter_map(|(name, (id, hey))| {
            egraph.eq(&id, &needle_id).then(|| {
                let proof = egraph.explain_equivalence(hey.clone(), needle.clone());
                (name, (hey, proof.to_flat_string(&egraph)))
            })
        })
        .collect()
}

fn parse_ty(ty: &str) -> RecExpr<Type> {
    RecExpr::parse(&ty.replace("forall", "∀").replace("->", "→")).unwrap()
}

fn parse_signature_line(line: &str) -> (String, RecExpr<Type>) {
    let mut line = line.split(":");
    let name = line.next().unwrap().trim();
    let ty = line.next().unwrap().trim();
    (name.to_string(), parse_ty(ty))
}

fn parse_signatures(path: String) -> HashMap<String, RecExpr<Type>> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(parse_signature_line)
        .collect()
}

fn main() {
    use easy_repl::{CommandStatus, Repl, command};

    let path = std::env::args()
        .nth(1)
        .expect("Expected path to signature file");
    let signatures = parse_signatures(path);
    let mut repl = Repl::builder()
        .add(
            "search",
            easy_repl::command! {
                "Search library items by query type",
                (ty: String) => |ty: String| {
                    let ty = RecExpr::parse(ty.trim()).unwrap();
                    let matches = search(&signatures, ty);
                    for (name, (ty, proof)) in matches {
                        println!("{name}: {ty}\n\nExplanation:\n{proof}\n");
                    }
                    Ok(easy_repl::CommandStatus::Done)
                }
            },
        )
        .build()
        .unwrap();
    repl.run().unwrap();
}
