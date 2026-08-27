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
#let interpret = $class("binary", triangle.r.small)$
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
#let LogicGrz = Logic("Grz")
#let LogicKT = Logic("KT")

// Intuitionistic modal logics
#let LogiciK = Logic("iK")
#let LogiciGL = Logic("iGL")
#let LogiciSL = Logic("iSL")

// Polymodal provability logic and its strictly positive fragments
#let LogicGLP = Logic("GLP")
#let LogicRC = Logic("RC")
#let LogicWC = Logic("WC")
#let LogicQRC1 = $Logic("QRC"_1)$

#let Gentzen(L) = $cal("G")_(#L)$
#let GentzenGL = Gentzen(LogicGL)
#let GentzenGLPoint3 = Gentzen(LogicGLPoint3)
#let GentzenGrz = Gentzen(LogicGrz)

#let GentzenS = Gentzen(LogicS)
#let GentzenD = Gentzen(LogicD)

#let GentzenWithCutGL = $Gentzen(LogicGL) + ("Cut")$
#let GentzenWithCutGrz = $Gentzen(LogicGrz) + ("Cut")$
#let GentzenWithCutS = $Gentzen(LogicS) + ("Cut")$
#let GentzenWithCutD = $Gentzen(LogicD) + ("Cut")$

// Levelled sequent arrows of the sequent calculi for S and D
#let seq(l) = $attach(tr: #l, =>)$
#let seq1 = seq("1")
#let seq2 = seq("2")
#let seq3 = seq("3")

#let Hilbert(L) = $cal("H")_(#L)$
#let HilbertGL = Hilbert(LogicGL)
#let HilbertGrz = Hilbert(LogicGrz)

#let Prov(T) = $attach(br: #T, sans("Prov"))$
// Use for *standard* provability predicate
#let Pr(T) = $attach(br: #T, sans("Pr"))$

#let height(T) = $upright("hgt")(#T)$

#let GoedelNum(x) = $corner.l #x corner.r$
#let True(x) = $sans("True")(#x)$
#let TruePartial(Gamma, x) = $sans("True")_(#Gamma) (#x)$
#let ProvLogic(T, U) = $upright("PL")_(#T) (#U)$

#let Theory(T) = $sans(upright(#T))$
#let PeanoArithmetic = Theory("PA")
#let TrueArithmetic = Theory("TA")
#let HeytingArithmetic = Theory("HA")

#let Axiom(A) = $upright(#A)$
#let AxiomK = $Axiom("K")$
#let AxiomL = $Axiom("Löb")$
#let AxiomT = $Axiom("T")$
#let AxiomGrz = $Axiom("Grz")$

#let System(X) = $bold(#X)$

#let LK1 = $System("LK")^1$
#let LOR = $cal(L)_"OR"$
#let Ind(x) = $sans("I")#x$
#let ISigma1 = $Ind(Sigma_1)$
#let Robinson = $sans("Q")$
#let R0 = $sans("R"_0)$
#let Con(T) = $sans("Con")_(#T)$

#let Bew = $class("unary", frak("B"))$
#let Wid = $class("unary", frak("W"))$

#let sepWithCommaMath(..args) = args.pos().join[,]

#let brak(..args) = $lr(chevron.l sepWithCommaMath(..args) chevron.r)$
#let quant(Q, ..args) = $#Q sepWithCommaMath(..args) space.narrow$
#let fal(..args) = $quant(forall, ..args)$
#let exs(..args) = $quant(exists, ..args)$
#let nexs(..args) = $quant(exists.not, ..args)$
#let exsUniq(..args) = $quant(exists!, ..args)$

#let godel(x) = $lr(⌜ #x ⌝)$
