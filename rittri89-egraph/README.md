# Rittri89-egraph

Like [Rittri89](../Rittri89), but implemented using (slotted) e-graphs and made to emit isomorphism proofs.

```math
\begin{align*}
  A \times (B \times C) & = (A \times B) \times C \\
  A \times B & = B \times A \\
  A \times 1 & = A \\
  A \rightarrow (B \rightarrow C) & = (A \times B) \rightarrow C \\
  1 \rightarrow A & = A \\
  A \rightarrow (B \times C) & = (A \rightarrow B) \times (A \rightarrow C) \\
  A \rightarrow 1 & = 1
\end{align*}
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
