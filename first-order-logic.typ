#import "./notations.typ": *

= Mechanization of the incompleteness theorems

私達が mechanize した結果は次の二つである．

#theorem[Gödel's First Incompleteness Theorem][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound $LOR$-theory stronger than $R0$,
  Then $T$ is incomplete,
  that is, there exists a $LOR$-sentence $phi$ such that $T nproves phi$ and $T nproves not phi$.
]

#theorem[Gödel's Second Incompleteness Theorem][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound $LOR$-theory stronger than $ISigma1$.
  Then $T nproves Con(T)$,
  where $Con(T)$ is a consistency statement of $T$.
]

証明の大筋は既存の標準的な手法（例えば @HajekPudlak2016 を参照）を大きく逸脱しない．
そのため，詳細な説明は省略するが，いくつか technical, methodological な点について注釈する．

=== Syntax
一階述語論理の term や formula の表現のために，我々は locally nameless representation を採用する．
同様の手法は @HvD20 でも用いられている．

これは標準的な logic の言葉では term や formula を拡大した概念である _semiterm_ および _semiformula_ @Buss1998 を用いることに対応する．
変数記号は2種類(free-variables, denoted by $\&x, "for" x in xi$ and bound-variables, denoted by $\#z, "for" z in [n]$) に分けられ，
semiterm とはこれらを変数として生成される term である．
semiformula は通常のように semiterm から生成される formula であるが，量化子によって束縛されない bound-variables を含みうる．
私達は type $xi$ の free-variables と $n$ 個の bound-variables を含みうる semiformula の為す型を `Semiterm ξ n` として形式化した．

#leancode(links: (
  ("Foundation", "Foundation/FirstOrder/Basic/Syntax/Formula.lean#L24-L32"),
  ),
  note:[
    We write `Formula L ξ` for `Semiformula L ξ 0`, and `Sentence L` for sentences, namely `Formula L Empty`.
  ])[
  ```
  inductive Semiformula (L : Language) (ξ : Type*) :
      ℕ → Type _ where
  |  verum : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |    and : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |     or : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n
  ```
]

Semiformula を用いた形式化は， formula の定義のための単なる技術的技工であるだけでなく，practical な利点も持つ．
例えば， $M$-parameter を持つ論理式 $A[x, y, z]$, というような，証明論やモデル論で頻出する制限は，
ただ一つの type `Semiformula M 3` によって与えることができる．

=== On internal argument
多くの場合， incompleteness theorems (特に G2) の証明に於いて障害となるのは，
しばしば arithmetization や bootstrapping と呼ばれる，メタ数学（項，論理式，証明可能性，初等的な証明論，etc.）の internalization,
すなわち，形式化した証明体系（ここでは $ISigma1$）の内部でこれらの概念を形式的に定義・証明することである．
この作業をナイーブに syntactical に行おうとする試みは，次に述べる理由によって阻害される#footnote[
  しかし， これを達成する意義は十分にある．
  これらの syntactic な操作は constructive で，かつ非常に弱い base theory (e.g. $sans("S")^1_2$)で行うことができる．
]．

/ 証明体系の煩雑さ: 十分に複雑な論理式を扱うにあたって，証明体系は手に負えないほど複雑になりうる．
  Lean 上で形式的に扱うのでさえ困難な作業を，その内部で定義された，更に制限された形式体系で行うのは苦痛である．
  更に，私達はその内部で形式化されたメタ数学概念（e.g. 形式化された証明可能性）を扱わなくてはならない．これはほとんど現実的ではない．
/ _internalization_ の non-cannonical 性:
  Bootstrapping の対象は主にメタ数学の形式化である．
  このために概念のコード化，しばしば Gödel numberization という作業を行う．
  不運なことに，これらに canonnical な選択や数学的に自然な唯一の方法というものはなく，
  単純に複雑な，そして膨大な組み合わせ論（しばしば大量のアドホックな構成を持つ）を用いなければならない．
  これは証明を複雑にし，先に述べた理由によって mechanization を困難にする．

ここで用いた打開策は completeness theorem を用いた model-theoretic argument によって syntax の bureaucracy を回避することである．
これは前者の問題をほぼ解決する．後者の問題は完全には解決されないが，その複雑さはいくらか緩和される．

== Proof sketch

=== Arithmetic

第二不完全性定理を証明するにあたって基礎となる体系として，ここでは $ISigma1$ を選ぶ．
これは実際には過剰に強い理論であり， より強い結果を得たいならば理論を弱めて
Buss's theory $sans("S")^1_2$ でも標準的な証明はほとんど同様に#footnote[
  Derivability condition D3 は多くの証明（私達が採用した証明も含む）では，
  formalized $Sigma_1$-completeness によって証明されるが，
  これは $sans("S")^1_2$ で成立するかは未解決な問題である @Bek2006．
  このため，よりシャープな formalized $Sigma^"b"_1$-completeness を証明する必要がある．
]実行可能である．
加えて， Nelson による interpretation $Robinson triangle.small.r sans("S")^1_2$ を用いれば，
第二不完全性定理は Robinson arithmetic $Robinson$ を interpret する広範な理論に拡大できる @Vis2011．
これは魅力的な方向性ではあるが，形式化があまりにも複雑になることからこの道は選ばない．
$ISigma1$ では @thm:recursive-def が成立するため帰納的な述語及び関数の定義が扱うことが楽である．

#theorem[$ISigma1$][
  Let $Phi(bold(C); arrow(v), x)$ be a predicate over $bold(V)$ which takes a class $bold(C) subset.eq bold(V)$ as a parameter.
  Assume that this satisfies following conditions.
  / Definability: A predicate $P(c, arrow(v), x) := Phi({z | z in c}; arrow(v), x)$ is $Delta_1$-definable.
  / Monotonicity: $bold(C) subset.eq bold(C')$ and $Phi(bold(C); arrow(v), x)$ implies $Phi(bold(C'); arrow(v), x)$.
  / Finiteness: If $Phi(bold(C); arrow(v), x)$ holds, then there is $m in V$, such that $Phi({z in bold(C) | z < m}; arrow(v), x)$ holds.

  Then we have a $Sigma_1$-definable predicate $"Fix"_Phi (arrow(v), x)$ such that
  $
    "Fix"_Phi (arrow(v), x) <==> Phi({z | "Fix"_Phi (arrow(v), z)}; arrow(v), x)
  $
  Additionally, if it satisfies following condition, $"Fix"_Phi (arrow(v), x)$ is $Delta_1$-definable.
  / Strong finiteness: If $Phi(bold(C); arrow(v), x)$ holds, then $Phi({z in bold(C) | z < x}; arrow(v), x)$ holds.

]<thm:recursive-def>

== Bootstrapping

== Incompleteness Theorems
