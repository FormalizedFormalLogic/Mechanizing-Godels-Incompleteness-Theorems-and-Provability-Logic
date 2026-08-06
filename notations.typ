#import "init.typ": *
#show: thmrules

#let dand = $⩕$
#let dor = $⩖$

#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)

= General math symbols

#let Nat = $bb(N)$
#let Rat = $bb(Q)$
#let Real = $bb(R)$
#let Bool = $bb(B)$

#let family(x) = $cal(#x)$
#let PowerSet = $cal(upright("P"))$
#let nle = $lt.eq.not$
#let And = $class("relation", \&)$
#let Not = $class("normal", "not")$
#let Or = $class("relation", "or")$
#let Implies = $class("relation", "implies")$
#let sim = $class("unary", \~)$



#let proves = $class("relation", tack.r)$
#let nproves = $class("relation", tack.r.not)$

#let models = $class("relation", tack.rr)$
#let nmodels = $class("relation", tack.rr.not)$

#let Box = $class("unary", square)$
#let Boxdot = $class("unary", ⊡)$
#let Dia = $class("unary", diamond)$
#let land = $and$
#let limp = $->$
#let liff = $<->$
#let lor = $or$
#let lnot = $not$

#let Prop = $upright("Prop")$

#let Logic(L) = $sans(upright(#L))$
#let sumQuasiNormal(L1, L2) = $#L1 + #L2$
#let LogicD = Logic("D")
#let LogicA = Logic("A")
#let LogicGLPoint3 = Logic("GL.3")
#let LogicGLAlpha(a) = $Logic("GL")_(#a)$
#let LogicGLBetaMinus(b) = $Logic("GL")_(#b)^-$
#let trace(x) = $upright("tr")(#x)$
#let subfml(A) = $upright("Sub")(#A)$
#let prebox(X) = $Box^(-1) #X$

#let LogicS4 = Logic("S4")
#let LogicGL = Logic("GL")
#let LogicGLPlusBoxBot(n) = $LogicGL + Box^#n bot$
#let LogicS = Logic("S")

#let Gentzen(L) = $cal("G")_(#L)$
#let Hilbert(L) = $cal("H")_(#L)$
#let GentzenGL = Gentzen(LogicGL)
#let GentzenWithCutGL = $Gentzen(LogicGL) + ("Cut")$
#let HilbertGL = Hilbert(LogicGL)
#let GentzenGLPoint3 = Gentzen(LogicGLPoint3)

#let Prov(T) = $attach(br: #T, upright("Prov"))$
// Use for *standard* provability predicate
#let Pr(T) = $attach(br: #T, upright("Pr"))$

#let height(T) = $upright("hgt")(#T)$

#let GoedelNum(x) = $corner.l #x corner.r$
#let ProvLogic(T, U) = $upright("PL")_(#T) (#U)$

#let Theory(T) = $sans(upright(#T))$
#let PeanoArithmetic = Theory("PA")
#let TrueArithmetic = Theory("TA")

#let Axiom(A) = $upright(#A)$
#let AxiomK = $Axiom("K")$
#let AxiomL = $Axiom("Löb")$
#let AxiomT = $Axiom("T")$

#let System(X) = $bold(#X)$

#let LK1 = $System("LK")^1$
#let LOR = $cal(L)_"OR"$
#let ISigma1 = $sans("I")Sigma_1$
#let Robinson = $sans("Q")$
#let R0 = $sans("R"_0)$
#let Con(T) = $sans("Con")_(#T)$
