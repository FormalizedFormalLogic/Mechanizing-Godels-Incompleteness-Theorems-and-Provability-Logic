#import "./notations.typ": *

= Provability Logic

このセクションではSolovay @solovay1976 の算術的完全性の形式化について紹介する．
定義や事実は，引き続き紹介のために必要な最小限かつある程度インフォーマルに紹介する．
様相論理としては，ゲーデル-レーブの論理 #Logic("GL") や，ソロベイの非正規論理 #Logic("S") の定義と，Kripke意味論に対する完全性を述べる．
次に算術的解釈などを導入し，最後にSolovayの算術的完全性定理を述べる．
証明や詳細に関しては，様相論理については @chagrovModalLogic2001 を，証明可能性論理については @boolosLogicProvability1994 などを参照しなさい．

様相論理の論理式は命題変数 #Prop とプリミティブな論理結合子 $bot, limp$，様相演算子 $Box$ を用いて定義される．
他の演算子 $top, lnot, land, lor, Dia$ は通常通りの略記として導入するものとする．

#definition[
  ゲーデル-レーブの様相論理 #Logic("GL") は，以下の公理と規則によってHilbert流で定義される論理である．
  #grid(
    columns: 2,
    column-gutter: 16pt,
    align: top,
    [
      1. 命題論理のトートロジー
      2. 公理 $upright("k")$: $Box(p -> q) -> (Box p -> Box q)$
      3. 公理 $upright("löb")$: $Box(Box p -> p) -> Box p$
    ],
    [
      4. #prooftree(rule(name: "MP", $B$, $A -> B$, $B$))
      5. #prooftree(rule(name: "Nec", $Box A$, $A$))
      6. #prooftree(rule(name: "Subst", $A[p := B]$, $A$))
    ],
  )
]

#definition[
  ソロベイの論理 #Logic("S") は，#Logic("GL") の全ての定理と公理 $upright("t")$: $Box p -> p$ に関して，モダスポネンスと代入規則で閉包を取ることで得られる非正規論理である．
]

様相論理の標準的な意味論であるKripke意味論を導入する．

#definition[
  Kripkeモデルとは $chevron.l W, R, V chevron.r$ であって，$W$ は非空集合，$R subset.eq W times W$，$V : Prop -> W -> 2$ である．
  モデルについて以下の用語を定める．
  - モデルが有限であるとは，$W$ が有限集合であることをいう．
  - モデルの根 $r in W$ とは，任意の $x != r$ となる $x in W$ に対して $r R x$ となる点 $r$ のことである．根が存在するモデルをrooted modelと呼ぶ．
  - モデルが推移的(transitive)とは，任意の $x, y, z in W$ に対して $x R y$ かつ $y R z$ ならば $x R z$ となることをいう．
  - モデルが非反射的(irreflexive) とは，任意の $x in W$ に対して $x R x$ でないことをいう．
]

我々はまず #LogicGL のKripke完全性を形式化した．
ただし，算術的完全性定理のために，単なるKripke完全性ではなく，rootedなモデルに対してのKripke完全性を示す必要がある．rootedなモデルへ変形する処理はTree Unravelingと呼ばれる方法を用いて行う (cf. @chagrovModalLogic2001[Theorem 3.18])．

#theorem[#LogicGL のKripke完全性][
  $Logic("GL") proves A$ であることと，任意の推移的，非反射的，rootedな有限モデル $M$ の根 $r$ で $r forces A$ であることは同値である．
]

以降では推移的かつ非反射的なモデルを #Logic("GL")-モデルと呼ぶことにする．
様相論理 #Logic("S") は非正規論理であるが，tailモデルと呼ばれるある程度よい性質を持った無限Kripkeモデルと同様の完全性が成り立つ．
/*
#Logic("GL") のrootedな有限モデルに対して，その根から $omega + 1$-個の点を伸ばし，付置を適当に拡張したモデルを考える．
このモデルはtail modelと呼ばれ，有限ではないが #Logic("GL")-モデルである．と，#Logic("S") で証明できることと全てのテイルモデルの根で妥当であることが同値になる．
*/
この事実は #Logic("S") の算術的完全性を議論する上で重要だが，ここでは詳しく説明しない．
テイルモデルの議論については @Visser1984 などを参照されたい．

次に，様相論理式を算術へ移すための算術的解釈を定義する．
全体を通し，$T, U$ は #PeanoArithmetic を適当に拡張した理論とする．


#definition[
  写像 $f colon Prop -> upright("Sent")_upright("A")$ をArithmetic Realizationと呼ぶ．
  解釈 $f$ と，証明可能性述語 $Prov(T)(x)$ によって，様相論理式 $A$ を次のように算術の文 $f_(Prov(T))(A)$ へと移すように拡張した写像をArithmetic Interpretationと呼ぶ．
  $
         f_(Prov(T)) (p) & = f(p) \
       f_(Prov(T)) (bot) & = bot \
    f_(Prov(T)) (A -> B) & = f_(Prov(T)) (A) -> f_(Prov(T)) (B) \
     f_(Prov(T)) (Box A) & = Prov(T) (GoedelNum(f_(Prov(T))(A)))
  $
  今考えている証明可能性述語 $Prov(T)$ が文脈上明らかな場合は単に省略して $f(A)$ と書くことにする．
]


我々は，特に証明可能性述語としてここでは標準的なもの $Pr(T)$ のみを考える．


#definition[
  $T$ の $U$ に対しての（標準的な）証明可能性論理 (standard provability logic of $T$ relative to $U$) を $ProvLogic(T, U)$ と書くことにして次のように定義する．
  $
    ProvLogic(T, U) = { A | #text[ $U proves f_(Pr(T)) (A)$ for any relaization $f$ ] }
  $
]

Solovayの算術的完全性定理とは，標準的な証明可能性述語の働きを単に演算子のように見ると，それは様相論理 #Logic("GL") によって正確に捉えられるということを主張する定理である．
別な言い方をすれば，適当な $T, U$ のセッティングにおいては，$ProvLogic(T, U)$ が #Logic("GL") と一致するということである．
ここでは，Visser @Visser1981 による理論の高さという概念を用いて，$T, U$ をある程度一般化した形で算術的完全性定理を紹介する．


#definition[Height of Theory][
  $n >= 1$ に対して，$n$ 回の証明可能性述語 $Prov(T)$ のイテレーションを $Prov(T)^n$ と書くことにする．
  理論 $T$ の高さ $height(T) <= omega$ とは，$T proves Prov(T)^n (GoedelNum(bot))$ となる最小の $n in omega$ である．ただし，そのような $n$ が存在しない場合は $height(T) = omega$ とする．
]

$T$ が $Sigma_1$ 健全であるときは $T$ の高さは $omega$ であることを注意しておく．

#definition[
  $n <= omega$ に対し #LogicGLPlusBoxBot($n$) を，$n < omega$ なら，#LogicGLPlusBoxBot($n$) を #LogicGL の定理に論理式 $Box^n bot$ を加えてモダスポネンスと代入で閉包を取った非正規な様相論理とし，$n = omega$ なら #LogicGL と定義する．
]

#theorem[@Visser1981][
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$．
] <thm:arithmetical_completeness>

この系として，ソロベイのオリジナルの主張を得る．

#corollary[Solovayの算術的完全性定理1 @solovay1976][
  $T$ が $Sigma_1$ 健全であるとき，$ProvLogic(T, T) = LogicGL$．
]

@thm:arithmetical_completeness は，$LogicGLPlusBoxBot(height(T)) nproves A$ だった場合に反例として得られる適当な高さの #Logic("GL")-モデルを算術に埋め込むことで証明される．

更に，Solovayは #Logic("S") が真の算術と算術的完全性になることも示した．

#theorem[Solovayの算術的完全性定理2 @solovay1976][
  $ProvLogic(T, sans("TA")) = Logic("S")$．
  つまり，任意の $A$ に対して，$Logic("S") proves A$ であることと，任意の算術的解釈 $f$ に対して $NN models f_(Pr(T)) (A)$ であることは同値である．
]
