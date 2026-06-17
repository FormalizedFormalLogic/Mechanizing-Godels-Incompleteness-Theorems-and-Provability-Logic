#import "./notations.typ": *

= Provability Logic

/*
このセクションではSolovay @solovay1976 の算術的完全性の形式化について紹介する．
定義や事実は，引き続き紹介のために必要な最小限かつある程度インフォーマルに紹介する．
様相論理としては，ゲーデル-レーブの論理 #Logic("GL") や，ソロベイの非正規論理 #Logic("S") の定義と，Kripke意味論に対する完全性を述べる．
次に算術的解釈などを導入し，最後にSolovayの算術的完全性定理を述べる．
証明や詳細に関しては，様相論理については @chagrovModalLogic2001 を，証明可能性論理については @boolosLogicProvability1994 などを参照しなさい．
*/
In this section we present our mechanization of Solovay's arithmetical completeness theorem @solovay1976.
As before, definitions and facts are introduced minimally, and are stated somewhat informally.
On the modal logic side, we give the definitions of the Gödel–Löb logic #LogicGL and of Solovay's non-normal modal logic #LogicS, and we state their completeness with respect to Kripke semantics.
We then introduce the arithmetical interpretation and related notions, and finally state Solovay's arithmetical completeness theorem.
For proofs and further details, the reader is referred to standard text @chagrovModalLogic2001 for modal logic and to @boolosLogicProvability1994 or survey @artemovProvabilityLogic2005 @japaridzeLogicProvability1998 for provability logic.

/*
様相論理の論理式は命題変数 #Prop とプリミティブな論理結合子 $bot, limp$，様相演算子 $Box$ を用いて定義される．
他の演算子 $top, lnot, land, lor, Dia$ は通常通りの略記として導入するものとする．
*/
Formulas of modal logic are defined from propositional variables (denotes #Prop), the primitive logical connectives $bot$ and $limp$, and the modal operator $Box$.
The remaining operators $top, lnot, land, lor, Dia$ are introduced as the usual abbreviations.

#definition[
  /* ゲーデル-レーブの様相論理 #Logic("GL") は，以下の公理と規則によってHilbert流で定義される論理である． */
  The Gödel–Löb modal logic #LogicGL is the logic defined in Hilbert style by the following axioms and rules.
  #grid(
    columns: 2,
    column-gutter: 16pt,
    align: top,
    [
      1. Tautologies of propositional logic /* 命題論理のトートロジー */
      2. Axiom $AxiomK$: $Box(p -> q) -> (Box p -> Box q)$
      3. Axiom $AxiomL$: $Box(Box p -> p) -> Box p$
    ],
    [
      4. #prooftree(rule(name: "MP", $B$, $A -> B$, $B$))
      5. #prooftree(rule(name: "Nec", $Box A$, $A$))
      6. #prooftree(rule(name: "Subst", $A[p := B]$, $A$))
    ],
  )
]

#definition[
  /* ソロベイの論理 #Logic("S") は，#Logic("GL") の全ての定理と公理 $AxiomT$: $Box p -> p$ に関して，モダスポネンスと代入規則で閉包を取ることで得られる非正規論理である． */
  Solovay's logic #LogicS is the non-normal logic obtained by closing all theorems of #LogicGL together with the axiom $AxiomT$: $Box p -> p$ under modus ponens and the substitution rule.
]

/* 様相論理の標準的な意味論であるKripke意味論を導入する． */
We introduce Kripke semantics, the standard semantics for modal logic.

#definition[
  /*
  Kripkeモデルとは $chevron.l W, R, V chevron.r$ であって，$W$ は非空集合，$R subset.eq W times W$，$V : Prop -> W -> 2$ である．
  モデルについて以下の用語を定める．
  - モデルが有限であるとは，$W$ が有限集合であることをいう．
  - モデルの根 $r in W$ とは，任意の $x != r$ となる $x in W$ に対して $r R x$ となる点 $r$ のことである．根が存在するモデルをrooted modelと呼ぶ．
  - モデルが推移的(transitive)とは，任意の $x, y, z in W$ に対して $x R y$ かつ $y R z$ ならば $x R z$ となることをいう．
  - モデルが非反射的(irreflexive) とは，任意の $x in W$ に対して $x R x$ でないことをいう．
  */
  A _Kripke model_ is a triple $chevron.l W, R, V chevron.r$, where $W$ is a nonempty set (called _points_), $R subset.eq W times W$, and $V : Prop -> W -> 2$ (called the _valuation_).
  We say the following terminology for models.
  - A model is _finite_ if $W$ is a finite set.
  - A _root_ of a model is a point $r in W$ such that $r R x$ for every $x in W$ with $x != r$. If a model has a root, we call it a _rooted model_.
  - A model is _transitive_ if, for all $x, y, z in W$, $x R y$ and $y R z$ imply $x R z$.
  - A model is _irreflexive_ if no $x in W$ satisfies $x R x$.
]

/*
我々はまず #LogicGL のKripke完全性を形式化した．
ただし，算術的完全性定理のために，単なるKripke完全性ではなく，rootedなモデルに対してのKripke完全性を示す必要がある．rootedなモデルへ変形する処理はTree Unravelingと呼ばれる方法を用いて行う (cf. @chagrovModalLogic2001[Theorem 3.18])．
*/
We first mechanized the Kripke completeness of #LogicGL.
We note that Kripke completeness of #LogicGL is already mechanized in HOL/Light by Maggesi and Pelini-Brogi @maggesiMechanisingGodelLob2023.
However, for the arithmetical completeness theorem, we need not merely Kripke completeness but Kripke completeness with respect to rooted models. The transformation into a rooted model is carried out by a method known as _tree unraveling_ (cf. @chagrovModalLogic2001[Theorem 3.18]).

#theorem[Kripke completeness of #LogicGL][
  /* $Logic("GL") proves A$ であることと，任意の推移的，非反射的，rootedな有限モデル $M$ の根 $r$ で $r forces A$ であることは同値である． */
  $LogicGL proves A$ if and only if $M, r forces A$ at the root $r$ of every transitive, irreflexive, rooted finite model $M$.
]

/*
この定理ゆえに，以降では推移的かつ非反射的な有限モデルを #Logic("GL")-モデルと呼ぶことにする．
いま，様相論理 #Logic("S") は非正規論理であるが，tailモデルと呼ばれるある程度よい性質を持った無限Kripkeモデルのクラスに対して，同様に根における完全性が成り立つ．
この事実は #Logic("S") の算術的完全性を議論する上で重要だが，ここでは詳しく説明しない．
テイルモデルの議論については @Visser1984 などを参照されたい．
*/
By this theorem, we henceforth call a transitive and irreflexive finite model a $LogicGL$-model.
Now, although the modal logic #LogicS is non-normal, an analogous rooted completeness holds with respect to a class of infinite Kripke models with reasonably good properties, called _tail models_.
This fact plays an important role in the discussion of the arithmetical completeness of #LogicS, but we do not show it here.
For a detail of tail models, see @Visser1984.

/*
次に，様相論理式を算術へ移すための算術的解釈を定義する．
全体を通し，$T, U$ は #PeanoArithmetic を適当に拡張した理論とする．
*/
We next define the arithmetical interpretation, which translates modal formulas into arithmetic sentences.
Throughout, $T$ and $U$ denote nice theories extending #PeanoArithmetic.

#definition[
  /*
  写像 $f colon Prop -> upright("Sent")_upright("A")$ をArithmetic Realizationと呼ぶ．
  解釈 $f$ と，証明可能性述語 $Prov(T)(x)$ によって，様相論理式 $A$ を次のように算術の文 $f_(Prov(T))(A)$ へと移すように拡張した写像をArithmetic Interpretationと呼ぶ．
  今考えている証明可能性述語 $Prov(T)$ が文脈上明らかな場合は単に省略して $f(A)$ と書くことにする．
  */
  A map $f colon Prop -> upright("Sent")_upright("A")$ is called an _arithmetic realization_ or shortly _realization_.
  Given a realization $f$ and a provability predicate $Prov(T)(x)$, the _arithmetic interpretation_ is the extension of $f$ that translates a modal formula $A$ into an arithmetic sentence $f_(Prov(T))(A)$ as follows:
  $
         f_(Prov(T)) (p) & = f(p) \
       f_(Prov(T)) (bot) & = bot \
    f_(Prov(T)) (A -> B) & = f_(Prov(T)) (A) -> f_(Prov(T)) (B) \
     f_(Prov(T)) (Box A) & = Prov(T) (GoedelNum(f_(Prov(T))(A)))
  $
  When the provability predicate $Prov(T)$ is obvious from context, we omit this and simply write $f(A)$.
]

/* 我々は，特に証明可能性述語としてここでは標準的なもの $Pr(T)$ のみを考える． */
In what follows, we consider only the standard provability predicate $Pr(T)$.

#definition[
  /*
  $T$ の $U$ に対しての（標準的な）証明可能性論理 (standard provability logic of $T$ relative to $U$) を $ProvLogic(T, U)$ と書くことにして次のように定義する．
  */
  The _(standard) provability logic of $T$ relative to $U$_, written $ProvLogic(T, U)$, is defined as follows:
  $
    ProvLogic(T, U) = { A | #text[ $U proves f_(Pr(T)) (A)$ for any realization $f$ ] }
  $
]

/*
Solovayの算術的完全性定理とは，標準的な証明可能性述語の働きを単に演算子のように見ると，それは様相論理 #Logic("GL") によって正確に捉えられるということを主張する定理である．
別な言い方をすれば，適当な $T, U$ のセッティングにおいては，$ProvLogic(T, U)$ が #Logic("GL") と一致するということである．
ここでは，Visser @Visser1981 による理論の高さという概念を用いて，$T, U$ をある程度一般化した形で算術的完全性定理を紹介する．
*/
Solovay's arithmetical completeness theorem states that the behavior of the standard provability predicate, regarded simply as a modal operator, is captured exactly by the modal logic #LogicGL.
In other words, for appropriate choices of $T$ and $U$, the provability logic $ProvLogic(T, U)$ coincides with #LogicGL.
Here we present the generalized version of the theorem, using the notion of the _height_ of a theory due to Visser @Visser1981.

#definition[Height of Theory][
  /*
  $n >= 1$ に対して，証明可能性述語 $Prov(T)$ の $n$ 回のイテレーションを $Prov(T)^n$ と書くことにする．
  理論 $T$ の高さ $height(T) <= omega$ とは，$T proves Prov(T)^n (GoedelNum(bot))$ となる最小の $n in omega$ である．ただし，そのような $n$ が存在しない場合は $height(T) = omega$ とする．
  */
  For $n >= 1$, we write $Pr(T)^n$ for the $n$-times iteration of the provability predicate $Pr(T)$.
  The _height_ of theory $T$, denoted $height(T) <= omega$, is the minimum $n in omega$ such that $T proves Pr(T)^n (GoedelNum(bot))$, or $omega$ if no such $n$ exists.
]

/* $T$ が $Sigma_1$ 健全であるときは $T$ の高さは $omega$ であることを注意しておく． */
Note that if $T$ is $Sigma_1$-sound, $T$ does not prove $Pr(T)^n (GoedelNum(bot))$ for any $n in omega$, therefore $height(T) = omega$.

#definition[
  /*
  $n <= omega$ に対し #LogicGLPlusBoxBot($n$) を，$n < omega$ なら，#LogicGLPlusBoxBot($n$) を #LogicGL の定理に論理式 $Box^n bot$ を加えてモダスポネンスと代入で閉包を取った非正規な様相論理とし，$n = omega$ なら #LogicGL と定義する．
  */
  For $n <= omega$, we define #LogicGLPlusBoxBot($n$) as follows: if $n < omega$, it is the non-normal modal logic obtained by closing all theorems of #LogicGL together with the formula $Box^n bot$ under modus ponens and the substitution rule; if $n = omega$, it is #LogicGL itself.
]

#theorem[@Visser1981][
  /* $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$． */
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$.
] <thm:arithmetical_completeness>

/*
@thm:arithmetical_completeness は，$LogicGLPlusBoxBot(height(T)) nproves A$ だった場合に反例として得られる適当な高さの #Logic("GL")-モデルを算術に埋め込むことで証明される．
*/
@thm:arithmetical_completeness is proved by embedding into arithmetic an appropriate $LogicGL$-model of suitable height, obtained as a countermodel when $LogicGLPlusBoxBot(height(T)) nproves A$.
/* この系として，ソロベイのオリジナルの主張を得る． */
As a corollary, we obtain Solovay's original statement.

#corollary[Solovay's Arithmetical Completeness Theorem 1 @solovay1976][
  /* $T$ が $Sigma_1$ 健全であるとき，$ProvLogic(T, T) = LogicGL$． */
  If $T$ is $Sigma_1$-sound, then $ProvLogic(T, T) = LogicGL$.
]

/* 更に，Solovayは #Logic("S") が真の算術と算術的完全性になることも示した． */
Solovay also proved that #LogicS is arithmetically complete with respect to true arithmetic #TrueArithmetic.

#theorem[Solovay's Arithmetical Completeness Theorem 2 @solovay1976][
  /*
  $ProvLogic(T, TrueArithmetic) = Logic("S")$．
  つまり，任意の $A$ に対して，$Logic("S") proves A$ であることと，任意の算術的解釈 $f$ に対して $NN models f_(Pr(T)) (A)$ であることは同値である．
  */
  $ProvLogic(T, TrueArithmetic) = LogicS$.
  That is, for any formula $A$, $LogicS proves A$ if and only if $NN models f_(Pr(T)) (A)$ for every arithmetic interpretation $f$.
]
