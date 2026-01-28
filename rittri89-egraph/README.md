# Rittri89-egraph

Like [Rittri89](../Rittri89), but implemented using (slotted) e-graphs and made to emit isomorphism proofs.

```rust
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
```

`cargo run -- signature.txt` to try it out.

```text
> search "(∀ $2 (∀ $1 (→ (→ (* (var $2) (var $1)) (var $2)) (→ (var $2) (→ (list (var $1)) (var $2))))))"
foldl: (∀ $1 (∀ $2 (→ (→ (var $1) (→ (var $2) (var $1))) (→ (var $1) (→ (list (var $2)) (var $1))))))

Explanation:
(∀ $f108 (∀ $f106 (→ (→ (var $f108) (→ (var $f106) (var $f108))) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))
(∀ $f108 (∀ $f106 (→ (Rewrite=> →-swap (→ (var $f106) (→ (var $f108) (var $f108)))) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))
(∀ $f108 (∀ $f106 (→ (Rewrite<= curry (→ (* (var $f106) (var $f108)) (var $f108))) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))
(∀ $f108 (∀ $f106 (→ (→ (Rewrite<= *-comm (* (var $f108) (var $f106))) (var $f108)) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))

foldr: (∀ $1 (∀ $2 (→ (→ (var $1) (→ (var $2) (var $2))) (→ (var $2) (→ (list (var $1)) (var $2))))))

Explanation:
(∀ $f122 (∀ $f120 (→ (→ (var $f122) (→ (var $f120) (var $f120))) (→ (var $f120) (→ (list (var $f122)) (var $f120))))))
(∀ $f122 (∀ $f120 (→ (Rewrite<= →-swap (→ (var $f120) (→ (var $f122) (var $f120)))) (→ (var $f120) (→ (list (var $f122)) (var $f120))))))
(Rewrite<= ∀-swap (∀ $f108 (∀ $f106 (→ (→ (var $f108) (→ (var $f106) (var $f108))) (→ (var $f108) (→ (list (var $f106)) (var $f108)))))))
(∀ $f108 (∀ $f106 (→ (Rewrite=> →-swap (→ (var $f106) (→ (var $f108) (var $f108)))) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))
(∀ $f108 (∀ $f106 (→ (Rewrite<= curry (→ (* (var $f106) (var $f108)) (var $f108))) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))
(∀ $f108 (∀ $f106 (→ (→ (Rewrite<= *-comm (* (var $f108) (var $f106))) (var $f108)) (→ (var $f108) (→ (list (var $f106)) (var $f108))))))
```
