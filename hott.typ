#import "template.typ": *
#import "typreset/lib.typ": font, thm-envs
#import "commute.typ": node, arr, commutative-diagram
#import "prooftrees/prooftrees.typ"
#import "prooftrees/internal.typ"
#import "@local/cetz:0.1.2"

#show: font.set-font.with(lang: "zh")

#let (theorem, definition, lemma, corollary, proof, proposition, example, convention, axiom) = thm-envs.presets()
#let thm-base = thm-envs.thm-base

#show: project.with(
  title: "同倫類型論",
  authors: (
    (name: "JoJo", email: "jojoid@duck.com"),
  ),
)

#let vdash = [⊢]

#set rect(stroke: .5pt)
#let mk_err_str(message) = "Prooftrees INTERNAL ERROR: " + message
#set table(stroke: none)
#let asmN = [assumption#sub[n]]
#let sans_font = "DejaVu Sans"
#let sans_font_opts = (font: sans_font, size: .82em)
#let tsans = (..args) => text(..sans_font_opts, ..args)

#let box_label(..text_opts, loc: top + left, inset: -2pt, b) = {
    place(loc, dx: inset, dy: inset, 
        tsans(size: .7em, ..text_opts)[#b])
}


#let horizons(..haligns) = haligns.pos().map(a => horizon + a)

= *$lambda$ 演算*

== *項*

#definition[
  *項*

  所有*項*的集合 $Lambda$ 的遞歸定義如下

  $1.$ （變量）$Lambda$ 中有無窮個變量；

  $2.$ （抽象）如果 $u$ 是一個變量且 $M in Lambda$，則 $(u.M) in Lambda$；

  $3.$ （應用）如果 $M, N in Lambda$，則 $("MN") in Lambda$.

  更簡短的表述是
  $
    Lambda := V | (V.Lambda) | (Lambda Lambda)
  $ 或 $
    M := u | (u.M) | (M N)
  $
  其中 $V$ 是變量集.
]

#definition[
  *子項*

  項 $M$ 的所有*子項*的集合定義爲 $op("Sub")(M)$，$op("Sub")$ 的遞歸定義如下

  $1.$ （基礎）對於任何變量 $x$，$op("Sub")(x) := {x}$；

  $2.$ （抽象） $op("Sub")(x.M) := op("Sub")(M) union {(x.M)}$；

  $3.$ （應用） $op("Sub")(M N) := op("Sub")(M) union op("Sub")(N) union {(M N)}$.
]

#lemma[
  $1.$ （自反性）對於任何項 $M$，有 $M in op("Sub")(M)$；

  $2.$ （傳遞性）如果 $L in op("Sub")(M)$ 且 $M in op("Sub")(N)$，則 $L in op("Sub")(N)$.
]

#lemma[
  項可以以樹表示給出，如下圖中的例子

  #align(
    center,
    cetz.canvas({
      import cetz.draw: *

      let data = ([ap], ([y]), ([$x.$], ([ap], [x], [z])))

      cetz.tree.tree(data, content: (padding: .1), line: (stroke: blue))
    })
  ) $ (y (x.(x z))) "的樹表示" $

  項的子項對應於項的樹表示的子樹.
]

#convention[
  $1.$ 最外層括號可以省略；

  $2.$ （抽象是右結合的） $x.y.M$ 是 $x.(y.M)$ 的一個縮寫；

  $3.$ （應用是左結合的） $M N L$ 是 $((M N) L)$ 的一個縮寫；

  $4.$ （應用優先於抽象）$x.M N$ 是 $x.(M N)$ 的一個縮寫.
]

== *自由和綁定變量*

#definition[
  *自由變量*

  項 $M$ 的所有*自由變量*的集合定義爲 $op("FV")(M)$，$op("FV")$ 的遞歸定義如下

  $1.$ （變量） $op("FV")(x) := {x}$；

  $2.$ （抽象） $op("FV")(x.M) :=
  op("FV")(M) backslash {x}$；

  $3.$ （應用） $op("FV")(M N) :=
  op("FV")(M) union op("FV")(N)$.
]

#example[
  $(y (x.(x z)))$ 的樹表示如下圖所示

  #align(
    center,
    cetz.canvas({
      import cetz.draw: *

      let data = ([ap], ([y]), ([$x.$], ([ap], [x], [z])))

      cetz.tree.tree(data, content: (padding: .1), line: (stroke: blue))
    })
  )

  $op("FV")(y (x.(x z))) = {y, z}.$
]

#definition[
  *閉項*

  一個項 $M$ 是*閉*的 $:<=> op("FV")(M) = emptyset$.

  所有閉項的集合記爲 $Lambda^0$.
]

== *$alpha$ 等價*

#definition[
  *重命名*

  將項 $M$ 中 $x$ 的每個自由出現都替換爲 $y$，結果記爲 *$M^(x -> y)$*.
]

#definition[
  *$alpha$ 等價*

  定義 *$alpha$ 等價* $scripts(=)_alpha$ 爲符合如下性質的關係

  $1.$ （重命名）如果 $y$ 不在 $M$ 中出現，則
  $x.M scripts(=)_alpha y.M^(x -> y)$；

  $2.$ （兼容性）如果 $M scripts(=)_alpha N$，則
  $M L scripts(=)_alpha N L$，$L M scripts(=)_alpha L N$ 且對於任何變量 $z$ 有 $z.M scripts(=)_alpha z.N$；

  $3.$ （自反性） $M scripts(=)_alpha M$；

  $4.$ （對稱性）如果 $M scripts(=)_alpha N$，則
  $N scripts(=)_alpha M$；

  $5.$ （傳遞性）如果 $L scripts(=)_alpha M$ 且 $M scripts(=)_alpha N$，則
  $L scripts(=)_alpha N$.
]

== *代入*

#definition[
  *代入*

  $(1a)$ $x[N slash x] := N$；

  $(1b)$ 如果 $x != y$，則
  $y[N slash x] := y$；

  $(2)$ $(P Q)[N slash x] := (P[N slash x])(Q[N slash x])$；

  $(3)$ 如果 $z.P^(y -> z) scripts(=)_alpha y.P$ 且 $z in.not op("FV")(N)$，則
  $(y.P)[N slash x] := z.(P^(y -> z)[N slash x])$.
]

#lemma[
  設 $x != y$ 且 $x in.not op("FV")(N)$，則
  $L[M, N slash x, y] = L[N, M[N slash y] slash x, y]$.
]

#definition[
  *同時代入*

  $M[N_1, ... , N_n slash x_1, ... , x_n]$ 表示把項 $N_1, ... , N_n$ *同時代入*到變量 $x_1, ... , x_n$.
]

#pagebreak()

= *類型論*

== *項*

#definition[
  *項*

  比 $lambda$ 演算多了一些常量以及新的構造.
]

== *語境*

#definition[
  *語境*

  一個*語境*是一個列表
  
  $
    x_1: A_1, x_2: A_2, ... , x_n: A_n
  $
  
  其中 $x_1, ... , x_n$ 是不同的變量，它們分別擁有類型 $A_1, ... , A_n$. 我們用 $Gamma, Delta$ 等字母來縮寫語境.
]

#definition[
  *語境規則*

  *$Gamma "ctx"$* 是一個判斷，表示“$Gamma$ 是良構的語境.”
  有如下規則

  #prooftrees.tree(
    prooftrees.axi[],
    prooftrees.uni(right_label: [$" ctx-EMP"$])[$dot "ctx"$],
  )

  #prooftrees.tree(
    prooftrees.axi[$x_1: A_1, x_2: A_2, ... , x_(n-1): A_(n-1) vdash A_n: cal(U)_i$],
    prooftrees.uni(right_label: [$" ctx-EXT"$])[$(x_1: A_1, ... , x_n: A_n) "ctx"$],
  )

  其中，變量 $x_n$ 與變量 $x_1, ... , x_n$ 中的任何一個都不同.
]

== *結構規則*

#definition[
  *$"Vble"$ 規則*
  
  #prooftrees.tree(
    prooftrees.axi[$(x_1: A_1, ... , x_n: A_n) "ctx"$],
    prooftrees.uni(right_label: [$" Vble"$])[$x_1: A_1, ... , x_n: A_n vdash x_i: A_i$],
  )
]

#definition[
  *判斷相等*

  $
    "如果" a scripts(=)_alpha b"，則" a eq.triple b.
  $

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.uni[$Gamma vdash a eq.triple a: A$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash a eq.triple b: A$],
    prooftrees.uni[$Gamma vdash b eq.triple a: A$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash a eq.triple b: A$],
      prooftrees.axi[$Gamma vdash b eq.triple c: A$],
    prooftrees.bin[$Gamma vdash a eq.triple c: A$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash A eq.triple B: cal(U)_i$],
    prooftrees.bin[$Gamma vdash a: B$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash a eq.triple b: A$],
      prooftrees.axi[$Gamma vdash A eq.triple B: cal(U)_i$],
    prooftrees.bin[$Gamma vdash a eq.triple b: B$],
  )
]

== *類型宇宙*

#definition[
  *類型宇宙層級*

  $
    cal(U)_0, cal(U)_1, cal(U)_2, ...
  $

  有如下規則
  
  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "cal(U)"-INTRO"$])[$Gamma vdash cal(U)_i: cal(U)_(i+1)$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
    prooftrees.uni(right_label: [$" "cal(U)"-CUMUL"$])[$Gamma vdash A: cal(U)_(i+1)$],
  )
]

== *依賴函數類型（$Pi$-類型）*

#definition[
  *依賴函數類型（$Pi$-類型）*

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma, x:A vdash B: cal(U)_i$],
    prooftrees.bin(right_label: [$" "Pi"-FORM"$])[$Gamma vdash (x: A) -> B : cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A_1 eq.triple A_2 : cal(U)_i$],
      prooftrees.axi[$Gamma, x:A_1 vdash B_1 eq.triple B_2: cal(U)_i$],
    prooftrees.bin(right_label: [$" "Pi"-FORM-EQ"$])[$Gamma vdash (x: A_1) -> B_1 eq.triple (x: A_2) -> B_2 : cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: A vdash b: B$],
    prooftrees.uni(right_label: $" "Pi"-INTRO"$)[$Gamma vdash (x: A) |-> b : (x: A) -> B$],
  )
  
  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: A vdash b_1 eq.triple b_2 : B$],
    prooftrees.uni(right_label: $" "Pi"-INTRO-EQ"$)[$Gamma vdash (x: A) |-> b_1 eq.triple (x: A) |-> b_2 : (x: A) -> B$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash f: (x: A) -> B$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.bin(right_label: [$" "Pi"-ELIM"$])[$Gamma vdash f(a): B[a slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash f_1 eq.triple f_2 : (x: A) -> B$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.bin(right_label: [$" "Pi"-ELIM-EQ"$])[$Gamma vdash f_1(a) eq.triple f_2(a) : B[a slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: A vdash b: B$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.bin(right_label: [$" "Pi"-COMP"$])[$Gamma vdash ((x: A) |-> b)(a) eq.triple b[a slash x]: B[a slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash f: (x: A) -> B$],
    prooftrees.uni(right_label: [$" "Pi"-UNIQ"$])[$Gamma vdash f eq.triple (x |-> f(x)) : (x: A) -> B$],
  )
]

#definition[
  *函數類型*

  設 $B: cal(U), x |-> B : A -> cal(U)$. 我們定義*函數類型*
  $
    A -> B :eq.triple (x: A) -> B.
  $
]

== *依賴序偶類型（$Sigma$-類型）*

#definition[
  *依賴序偶類型（$Sigma$-類型）*

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma, x:A vdash B: cal(U)_i$],
    prooftrees.bin(right_label: [$" "Sigma"-FORM"$])[$Gamma vdash (x: A) times B : cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A_1 eq.triple A_2 : cal(U)_i$],
      prooftrees.axi[$Gamma, x:A_1 vdash B_1 eq.triple B_2: cal(U)_i$],
    prooftrees.bin(right_label: [$" "Sigma"-FORM-EQ"$])[$Gamma vdash (x: A_1) times B_1 eq.triple (x: A_2) times B_2 : cal(U)_i$],
  )

  構造子（引入規則）：$angle.l "_" , "_" angle.r : {B: A -> cal(U)} -> (a: A) -> b: B(a) -> (x: A) times B$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: A vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : A$],
      prooftrees.axi[$Gamma vdash b_1 eq.triple b_2 : B[a slash x]$],
    prooftrees.tri(right_label: $" "Sigma"-INTRO-EQ"$)[$Gamma vdash (a_1, b_1) eq.triple (a_2, b_2) : (x: A) times B$],
  )

  消除器（消除規則）：$op("ind")_((x: A) times B) : [C: ((x: A) times B(x)) -> cal(U)] -> [(a: A) -> (b: B(a)) -> C(angle.l a,b angle.r)] -> [p: (x: A) times B(x)] -> C(p)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (x: A) times B vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A, y: B vdash g: C[(x, y) slash z]$],
      prooftrees.axi[$Gamma vdash p_1 eq.triple p_2 : (x: A) times B$],
    prooftrees.tri(right_label: $" "Sigma"-ELIM-EQ"$)[$Gamma vdash op("ind")_((x: A) times B)(z.C, x.y.g, p_1) eq.triple op("ind")_((x: A) times B)(z.C, x.y.g, p_2) : C[p_1 slash z] eq.triple C[p_2 slash z]$],
  )

  計算規則：$op("ind")_((x: A) times B) (C, g, angle.l a,b angle.r) :eq.triple op(g) (a) (b)$
]

#definition[
  *cartesian 類型*

  設 $B: cal(U), x |-> B : A -> cal(U)$. 我們定義*cartesian 類型*
  $
    A times B :eq.triple (x: A) times B.
  $
]

#lemma[
  *投影函數*

  對於任何 $Sigma$-類型 $(x: A) times B(x)$，我們有函數
  $
    op(bold("pr"_1)) : ((x: A) times B(x)) -> A, op(bold("pr"_1)) (angle.l a, b angle.r) :eq.triple a
  $ 和 $
    op(bold("pr"_2)) : (p: (x: A) times B(x)) -> B(op("pr"_1) (p)),
    op(bold("pr"_2)) (angle.l a, b angle.r) :eq.triple b.
  $
]

#proof[
  略.
]

== *餘積類型*

#definition[
  *餘積類型*

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash B: cal(U)_i$],
    prooftrees.bin(right_label: [$" "+"-FORM"$])[$Gamma vdash A + B : cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A_1 eq.triple A_2 : cal(U)_i$],
      prooftrees.axi[$Gamma vdash B_1 eq.triple B_2 : cal(U)_i$],
    prooftrees.bin(right_label: [$" "+"-FORM-EQ"$])[$Gamma vdash A_1 + B_1 eq.triple A_2 + B_2 : cal(U)_i$],
  )

  構造子 $1$：$op("inl") : {A, B: cal(U)} -> A -> A + B$

  構造子 $2$：$op("inl") : {A, B: cal(U)} -> B -> A + B$

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : A$],
    prooftrees.tri(right_label: [$" "+"-INTRO"_1"-EQ"$])[$Gamma vdash op("inl")(a_1) eq.triple op("inl")(a_2) : A + B$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash b_1 eq.triple b_2 : B$],
    prooftrees.tri(right_label: [$" "+"-INTRO"_2"-EQ"$])[$Gamma vdash op("inr")(b_1) eq.triple op("inr")(b_2) : A + B$],
  )

  消除器：$op("ind")_(A + B) : [C: (A + B) -> cal(U)] -> [(a: A) -> C(op("inl") (a))] -> [(b: B) -> C(op("inr") (b))] -> (e: A + B) -> C(e)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (A + B) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A vdash c: C[op("inl")(x) slash z]$],
      prooftrees.axi[$Gamma, y: B vdash d: C[op("inr")(y) slash z]$],
      prooftrees.axi[$Gamma vdash e_1 eq.triple e_2 : (A + B)$],
    prooftrees.quart(right_label: [$" "+"-ELIM-EQ"$])[$Gamma vdash op("ind")_(A + B)(z.C, x.c, y.d, e_1) eq.triple op("ind")_(A + B)(z.C, x.c, y.d, e_2) : C[e_1 slash z] eq.triple C[e_2 slash z]$],
  )

  計算規則 $1$：$op("ind")_(A + B) (C, g_0, g_1, op("inl") (a)) :eq.triple g_0 (a)$

  計算規則 $2$：$op("ind")_(A + B) (C, g_0, g_1, op("inr") (b)) :eq.triple g_1 (b)$
]

== *空類型 $0$*

#definition[
  *空類型 $bold(0)$*

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "bold(0)"-FORM"$])[$Gamma vdash bold(0): cal(U)_i$],
  )

  消除器：$op("ind")_(bold(0)) : (C: bold(0) -> cal(U)) -> (a: bold(0)) -> C(a)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(0) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : bold(0)$],
    prooftrees.bin(right_label: [$" "bold(0)"-ELIM-EQ"$])[$Gamma vdash op("ind")_(bold(0))(x.C, a_1) eq.triple op("ind")_(bold(0))(x.C, a_2) : C[a_1 slash x] eq.triple C[a_2 slash x]$],
  )
]

== *單元類型 $bold(1)$*

#definition[
  *單元類型 $bold(1)$*

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "bold(1)"-FORM"$])[$Gamma vdash bold(1): cal(U)_i$],
  )

  構造子：$ast.small : bold(1)$

  消除器：$op("ind")_(bold(1)) : (C: bold(1) -> cal(U)) -> C(ast.small) -> (x: bold(1)) -> C(x)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(1) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c: C[ast.small slash x]$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : bold(1)$],
    prooftrees.tri(right_label: [$" "bold(1)"-ELIM-EQ"$])[$Gamma vdash op("ind")_(bold(1))(x.C, c, a_1) eq.triple op("ind")_(bold(1))(x.C, c, a_2) : C[a_1 slash x] eq.triple C[a_2 slash x]$],
  )

  計算規則：$op("ind")_(bold(1)) (C, c, ast.small) :eq.triple c$
]

== *boolean 類型*

#definition[
  *boolean 類型*

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "bold(2)"-FORM"$])[$Gamma vdash bold(2): cal(U)_i$],
  )

  構造子 $1$：$0_bold(2) : bold(2)$

  構造子 $2$：$1_bold(2) : bold(2)$
  
  消除器：$op("ind")_(bold(2)) : (C: bold(2) -> cal(U)) -> C(0_bold(2)) -> C(1_bold(2)) -> (x: bold(2)) -> C(x)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(2) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c_0 : C[0_bold(2) slash x]$],
      prooftrees.axi[$Gamma vdash c_1 : C[1_bold(2) slash x]$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : bold(2)$],
    prooftrees.quart(right_label: [$" "bold(2)"-ELIM-EQ"$])[$Gamma vdash op("ind")_(bold(2))(x.C, c_0, c_1, a_1) eq.triple op("ind")_(bold(2))(x.C, c_0, c_1, a_2) : C[a_1 slash x] eq.triple C[a_2 slash x]$],
  )

  計算規則 $1$：$op("ind"_bold(2)) (C, c_0, c_1, 0_bold(2)) :eq.triple c_0$

  計算規則 $2$：$op("ind"_bold(2)) (C, c_0, c_1, 1_bold(2)) :eq.triple c_1$
]

== *自然數類型*

#definition[
  *自然數類型*

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "NN"-FORM"$])[$Gamma vdash NN: cal(U)_i$],
  )

  構造子 $1$：$0: NN$

  構造子 $2$：$op("succ") : NN -> NN$

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash n_1 eq.triple n_2 : NN$],
    prooftrees.uni(right_label: [$" "NN"-INTRO"_2"-EQ"$])[$Gamma vdash op("succ")(n_1) eq.triple op("succ")(n_2) : NN$],
  )

  消除器：$op("ind")_NN : (C: NN -> cal(U)) -> C(0) -> [(n: N) -> C(n) -> C(op("succ") (n))] -> (n: NN) -> C(n)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: NN vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c_0: C[0 slash x]$],
      prooftrees.axi[$Gamma, x: NN, y:C vdash c_s: C[op("succ")(x) slash x]$],
      prooftrees.axi[$Gamma vdash n_1 eq.triple n_2 : NN$],
    prooftrees.quart(right_label: [$" "NN"-ELIM-EQ"$])[$Gamma vdash op("ind")_NN (x.C, c_0, x.y.c_s, n_1) eq.triple op("ind")_NN (x.C, c_0, x.y.c_s, n_2) : C[n_1 slash x] eq.triple C[n_2 slash x]$],
  )

  計算規則 $1$：$op("ind")_NN (C, c_0, c_s, 0) :eq.triple c_0$

  計算規則 $2$：$op("ind")_NN (C, c_0, c_s, op("succ") (n)) :eq.triple op(c_s) (n, op("ind"_NN) (C, c_0, c_s, n))$
]

== *恆等類型*

#definition[
  *恆等類型*

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash b: A$],
    prooftrees.tri(right_label: [$" "="-FORM"$])[$Gamma vdash a scripts(=)_A b : cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : A$],
      prooftrees.axi[$Gamma vdash b_1 eq.triple b_2 : A$],
    prooftrees.tri(right_label: [$" "="-FORM-EQ"$])[$Gamma vdash a_1 scripts(=)_A b_1 eq.triple a_2 scripts(=)_A b_2 : cal(U)_i$],
  )

  構造子：$op("refl") : {A: cal(U)} -> (a: A) -> (a = a)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : A$],
    prooftrees.bin(right_label: [$" "="-INTRO-EQ"$])[$Gamma vdash "refl"_(a_1) eq.triple "refl"_(a_2) : a_1 scripts(=)_A a_1 eq.triple a_2 scripts(=)_A a_2$],
  )

  消除器：$op("ind")_(scripts(=)_A) : [C: (x, y : A) -> (x = y) -> cal(U)] -> [(x: A) -> C(x, x, "refl"_x)] -> (x, y : A) -> (p: x = y) -> C(x, y, p)$

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x:A, y:A, p: x scripts(=)_A y vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, z:A vdash c: C[z, z, "refl"_z slash x, y, p]$],
      prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash b: A$],
      prooftrees.axi[$Gamma vdash q_1 eq.triple q_2 : a scripts(=)_A b$],
    prooftrees.quint(right_label: [$" "="-ELIM-EQ"$])[$Gamma vdash op("ind")_(scripts(=)_A)(x.y.p.C, z.c, a, b, q_1) eq.triple op("ind")_(scripts(=)_A)(x.y.p.C, z.c, a, b, q_2) : C[a, b, q_1 slash x, y, p] eq.triple C[a, b, q_2 slash x, y, p]$],
  )

  計算規則：$op("ind")_(scripts(=)_A) (C, c, x, x, "refl"_x) :eq.triple c(x)$

  恆等類型的項稱爲*道路*；恆等類型的消除規則稱爲*道路歸納*.
]

== *定義*

#example[
  $compose :eq.triple
  (A: cal(U)_i) |-> (B: cal(U)_i) |-> (C: cal(U)_i) |-> (g: B -> C) |-> (f: A -> B) |-> (x: A) |-> g(f(x)).$
]

#pagebreak()

= *同倫類型論*

== *類型是高維羣胚*

#lemma[
  對於任何 $A: cal(U)_i, x,y: A$，都能構造一個函數 $op("_")^(-1): (x scripts(=)_A y) -> (y scripts(=)_A x)$ 使得 $("refl"_x)^(-1) eq.triple "refl"_x$.

  $p^(-1)$ 稱爲 $p$ 的*逆*.
]

#proof[
  第一種證明
  
  設 $A: cal(U)_i$，$D: (x,y: A) -> (x scripts(=)_A y) -> cal(U)_i, D(x,y,p) :eq.triple (y scripts(=)_A x)$.
  
  隨即我們就能構造一個函數 $d :eq.triple x |-> "refl"_x : (x: A) -> D(x, x, "refl"_x)$.
  
  然後根據恆等類型的消除規則我們有，對於任何 $x,y: A, p: (x scripts(=)_A y)$，可以構造項 $op("ind")_(scripts(=)_A) (D, d, x, y, p) : (y scripts(=)_A x)$.
  
  現在對於任何 $x, y : A$ 我們可以定義期望得到的函數 $op("_")^(-1) :eq.triple p |-> op("ind")_(scripts(=)_A) (D, d, x, y, p)$.
  
  由恆等類型的計算規則，得 $("refl"_x)^(-1) eq.triple "refl"_x$.
]

#proof[
  第二種證明

  對於每個 $x, y: A$ 和 $p: x = y$，我們想要構造一個項 $p^(-1): y = x$. 根據 $p$ 的道路歸納，我們只需要給出 $y$ 是 $x$ 且 $p$ 是 $"refl"_x$ 時的構造. 在該情況下，$"refl"_x$ 和 $"refl"_x^(-1)$ 的類型都是 $x = x$. 因此我們可以簡單地定義 $"refl"_x^(-1) :eq.triple "refl"_x$. 於是根據道路歸納，我們完成了構造.
]

#lemma[
  對於任何 $A: cal(U)_i, x,y,z: A$，都能構造一個函數 $square.filled.tiny: (x scripts(=)_A y) -> (y scripts(=)_A z) -> (x scripts(=)_A z)$ 使得 $"refl"_x op(square.filled.tiny) "refl"_x :eq.triple "refl"_x$.

  $p op(square.filled.tiny) q$ 稱爲 $p$ 和 $q$ 的*連接*.
]

#proof[
  第一種證明

  期望得到的函數擁有類型 $(x, y, z: A) -> (x scripts(=)_A y) -> (y scripts(=)_A z) -> (x scripts(=)_A z)$.

  我們將改爲定義一個函數，擁有和預期等價的類型 $(x, y: A) -> (x scripts(=)_A y) -> (z: A) -> (y scripts(=)_A z) -> (x scripts(=)_A z)$，這允許我們使用兩次恆等類型的消除規則.

  設 $D: (x, y: A) -> (x scripts(=)_A y) -> cal(U)_i, D(x,y,p) :eq.triple (z: A) -> (q: y scripts(=)_A z) -> (x scripts(=)_A z)$.

  然後，爲了對 $D$ 應用恆等類型的消除規則，我們需要類型爲 $(x: A) -> D(x, x, "refl"_x)$ 的函數，也就是類型爲 $(x, z: A) -> (q: x scripts(=)_A z) -> (x scripts(=)_A z)$.

  現在設 $E: (x, z: A) -> (q: x scripts(=)_A z) -> cal(U)_i, E(x, z, q) :eq.triple (x scripts(=)_A z)$.

  隨即我們能構造函數 $e :eq.triple x |-> "refl"_x : (x: A) -> E(x, x, "refl"_x)$.

  對 $E$ 應用恆等類型的消除規則，我們得到函數 $d: (x, z: A) -> (q: x scripts(=)_A z) -> E(x, z, q), x |-> z |-> q |-> op("ind")_(scripts(=)_A) (E, e, x, z, q)$.

  因爲 $E(x, z, q) eq.triple (x scripts(=)_A z)$，所以 $d: (x: A) -> D(x, x, "refl"_x)$.

  然後對 $D$ 應用恆等類型的消除規則我們有，對於任何 $x,y: A, p: (x scripts(=)_A y)$，可以構造項 $op("ind")_(scripts(=)_A) (D, d, x, y, p) eq.triple op("ind")_(scripts(=)_A) (D, (x, z: A) |-> (q: y scripts(=)_A z) |-> op("ind")_(scripts(=)_A) (E, e, x, z, q), x, y, p) : (z: A) -> (q: y scripts(=)_A z) -> (x scripts(=)_A z)$.

  於是我們有
  $
    (x, y: A) |-> (p: x scripts(=)_A y) |-> op("ind")_(scripts(=)_A) (D, (x, z: A) |-> (q: y scripts(=)_A z) |-> op("ind")_(scripts(=)_A) (E, e, x, z, q), x, y, p) :
  $$
    (x, y: A) -> (x scripts(=)_A y) -> (z: A) -> (y scripts(=)_A z) -> (x scripts(=)_A z)
  $

  現在對於任何 $a, b, c: A$ 我們可以定義期望得到的函數
  $
    square.filled.tiny :eq.triple (p: a scripts(=)_A b) |-> op("ind")_(scripts(=)_A) (D, (x: A) |-> (q: b scripts(=)_A c) |-> op("ind")_(scripts(=)_A) (E, e, x, c, q), a, b, p) :
  $$
    (a, b, c: A) -> (a scripts(=)_A b) -> (b scripts(=)_A c) -> (a scripts(=)_A c).
  $

  由恆等映射的計算規則，得
  $
    "refl"_a op(square.filled.tiny) "refl"_a eq.triple op("ind")_(scripts(=)_A) (D, (x: A) |-> op("ind")_(scripts(=)_A) (E, e, x, a, "refl"_a), a, a, "refl"_a) eq.triple op("ind")_(scripts(=)_A) (E, e, a, a, "refl"_a) eq.triple e(a) eq.triple "refl"_a.
  $
]

#proof[
  第二種證明

  對於每個 $x, y, z: A$，$p: x = y$ 和 $q: y = z$，我們想要構造一個項 $p op(square.filled.tiny) q : x = z$. 根據 $p$ 的道路歸納，我們只需要給出 $y$ 是 $x$ 且 $p$ 是 $"refl"_x$ 時的構造，即對於每個 $x, z: A$ 和 $q: x = z$，構造一個項 $"refl"_x op(square.filled.tiny) q : x = z$. 根據 $q$ 的道路歸納，只需給出 $z$ 是 $x$ 且 $q$ 是 $"refl"_x$ 時的構造，即對於每個 $x: A$，構造一個項 $"refl"_x op(square.filled.tiny) "refl"_x : x = x$. 因此我們可以簡單地定義 $"refl"_x op(square.filled.tiny) "refl"_x :eq.triple "refl"_x$. 於是根據道路歸納，我們完成了構造.
]

#lemma[
  設 $A: cal(U)_i$，$x, y, z, w : A$，$p: x = y$，$q: y = z$ 且 $r: z = w$. 我們有以下結論：

  $1.$ $p = p op(square.filled.tiny) "refl"_y$ 且 $p = "refl"_x op(square.filled.tiny) p$；

  $2.$ $p op(square.filled.tiny) p^(-1) = "refl"_x$ 且 $p^(-1) op(square.filled.tiny) p = "refl"_y$；

  $3.$ $(p^(-1))^(-1) = p$；

  $4.$ $p op(square.filled.tiny) (q op(square.filled.tiny) r) = (p op(square.filled.tiny) q) op(square.filled.tiny) r$.
]

#proof[
  所有證明都使用道路歸納.

  $1.$ 第一種證明：設 $D: (x, y : A) -> (p: x = y) -> cal(U), D(x, y, p) :eq.triple (p = p op(square.filled.tiny) "refl"_y)$. 那麼 $D(x, x, "refl"_x)$ 是 $"refl"_x = "refl"_x op(square.filled.tiny) "refl"_x$. 因爲 $"refl"_x op(square.filled.tiny) "refl"_x eq.triple "refl"_x$，我們有 $D(x, x, "refl"_1) eq.triple ("refl"_x = "refl"_x)$. 因此可以構造函數 $d :eq.triple x |-> "refl"_("refl"_x) : (x: A) -> D(x, x, "refl"_1)$. 根據道路歸納，對於每個 $x, y: A$ 和 $p: x = y$，我們有項 $op("ind")_(scripts(=)_A) (D, d, x, y, p) : p = p op(square.filled.tiny) "refl"_y$.

  本書後面將把 $op("ind"_(scripts(=)_A)) ((x,y,p) |-> (p = p op(square.filled.tiny) "refl"_y), x |-> "refl"_("refl"_x), x, y, p)$ 記爲 *$"ru"_p$*，把 $op("ind"_(scripts(=)_A)) ((x,y,p) |-> (p = "refl"_y op(square.filled.tiny) p), x |-> "refl"_("refl"_x), x, y, p)$ 記爲 *$"lu"_p$*.

  第二種證明：根據 $p$ 的道路歸納，只需要假設 $y$ 是 $x$ 且 $p$ 是 $"refl"_x$. 在該情況下，$p op(square.filled.tiny) "refl"_y eq.triple "refl"_x op(square.filled.tiny) "refl"_x eq.triple "refl"_x$. 因此只需證明 $"refl"_x = "refl"_x$，這是簡單的，即 $"refl"_("refl"_x) : "refl"_x = "refl"_x$.

  $2.$ 第一種證明：設 $D: (x, y : A) -> (p: x = y) -> cal(U), D(x, y, p) :eq.triple (p op(square.filled.tiny) p^(-1) = "refl"_x)$. 那麼 $D(x, x, "refl"_x)$ 是 $"refl"_x op(square.filled.tiny) "refl"_x^(-1) = "refl"_x$. 因爲 $"refl"_x^(-1) eq.triple "refl"_x$ 且 $"refl"_x op(square.filled.tiny) "refl"_x eq.triple "refl"_x$，我們有 $D(x, x, "refl"_x) eq.triple ("refl"_x = "refl"_x)$. 因此可以構造函數 $d :eq.triple x |-> "refl"_("refl"_x) : (x: A) -> D(x, x, "refl"_x)$. 根據道路歸納，對於每個 $x, y: A$ 和 $p: x = y$，我們有項 $op("ind")_(scripts(=)_A) (D, d, x, y, p) : p op(square.filled.tiny) p^(-1) = "refl"_x$.

  第二種證明：根據 $p$ 的道路歸納，只需要假設 $y$ 是 $x$ 且 $p$ 是 $"refl"_x$. 在該情況下，$p op(square.filled.tiny) p^(-1) eq.triple "refl"_x op(square.filled.tiny) "refl"_x^(-1) eq.triple "refl"_x$.

  $3.$ 第一種證明：設 $D: (x, y : A) -> (p: x = y) -> cal(U), D(x, y, p) :eq.triple (p^(-1))^(-1) = p$. 那麼 $D(x, x, p)$ 是 $("refl"_x^(-1))^(-1) = "refl"_x$. 因爲 $"refl"_x^(-1) eq.triple "refl"_x$，所以 $("refl"_x^(-1))^(-1) eq.triple "refl"_x^(-1) eq.triple "refl"_x$，那麼 $D(x, x, "refl"_x) eq.triple ("refl"_x = "refl"_x)$. 因此我們能構造函數 $d :eq.triple x |-> "refl"_("refl"_x) : (x: A) -> D(x, x, "refl"_x)$. 根據道路歸納，對於每個 $x, y: A$ 和 $p: x = y$，我們有項 $op("ind")_(scripts(=)_A) (D, d, x, y, p) : (p^(-1))^(-1) = p$.

  第二種證明：根據 $p$ 的道路歸納，只需要假設 $y$ 是 $x$ 且 $p$ 是 $"refl"_x$. 在該情況下，$(p^(-1))^(-1) eq.triple ("refl"_x^(-1))^(-1) eq.triple "refl"_x$.

  $4.$ 我們想要構造的函數的類型是 $(x, y, z, w : A) -> (p: x = y) -> (q: y = z) -> (r: z = w) -> (p op(square.filled.tiny) (q op(square.filled.tiny) r) = (p op(square.filled.tiny) q) op(square.filled.tiny) r)$，我們改爲證明 $(x, y : A) -> (p: x = y) -> (z: A) -> (q: y = z) -> (w: A) -> (r: z = w) -> (p op(square.filled.tiny) (q op(square.filled.tiny) r) = (p op(square.filled.tiny) q) op(square.filled.tiny) r)$.
  
  設 $D_1 : (x, y : A) -> (p: x = y) -> cal(U), D_1 (x, y, p) :eq.triple (z: A) -> (q: y = z) -> (w: A) -> (r: z = w) -> (p op(square.filled.tiny) (q op(square.filled.tiny) r) = (p op(square.filled.tiny) q) op(square.filled.tiny) r)$. 根據 $p$ 的道路歸納，只需要構造類型爲 $(x: A) -> D_1 (x, x, "refl"_x) eq.triple (x, z: A) -> (q: x = z) -> (w: A) -> (r: z = w) -> ("refl"_x op(square.filled.tiny) (q op(square.filled.tiny) r) = ("refl"_x op(square.filled.tiny) q) op(square.filled.tiny) r)$ 的函數.
  
  爲了構造這個類型的函數，我們設 $D_2 : (x, z: A) -> (q: x = z) -> cal(U), D_2(x, z, q) :eq.triple (w: A) -> (r: z = w) -> ("refl"_x op(square.filled.tiny) (q op(square.filled.tiny) r) = ("refl"_x op(square.filled.tiny) q) op(square.filled.tiny) r)$. 根據 $q$ 的道路歸納，只需要構造類型爲 $(x: A) -> D(x, x, "refl"_x) eq.triple (x, w: A) -> (r: x = w) -> ("refl"_x op(square.filled.tiny) ("refl"_x op(square.filled.tiny) r) = ("refl"_x op(square.filled.tiny) "refl"_x) op(square.filled.tiny) r)$ 的函數.
  
  爲了構造這個類型的函數，我們設 $D_3 : (x, w: A) -> (r: x = w) -> cal(U), D_3 (x, w, r) :eq.triple ("refl"_x op(square.filled.tiny) ("refl"_x op(square.filled.tiny) r) = ("refl"_x op(square.filled.tiny) "refl"_x) op(square.filled.tiny) r)$. 根據 $r$ 的道路歸納，只需要構造類型爲  $(x: A) -> D_3 (x, x, "refl"_x) eq.triple (x: A) -> ("refl"_x op(square.filled.tiny) ("refl"_x op(square.filled.tiny) "refl"_x) = ("refl"_x op(square.filled.tiny) "refl"_x) op(square.filled.tiny) "refl"_x) eq.triple (x: A) -> "refl"_x = "refl"_x$ 的函數. 這是簡單的，即 $"refl"_("refl"_x)$.
  
  因此，應用 $3$ 此道路歸納，我們就得到了想要的類型的函數.
]

#lemma[
  *加鬚*

  $1.$ 對於任何 $a, b, c : A, p, q : a = b$，我們可以構造函數 *$"_" op(square.filled.tiny_r) "_"$* $: (p = q) -> (r: b = c) -> (p op(square.filled.tiny) r = q op(square.filled.tiny) r), alpha op(square.filled.tiny_r) "refl"_b :eq.triple "ru"_p^(-1) op(square.filled.tiny) alpha op(square.filled.tiny) "ru"_q$；

  $2.$ 對於任何 $a, b, c : A, q, r : b = c$，我們可以構造函數 *$"_" op(square.filled.tiny_l) "_"$* $: (p: a = b) -> (r = s) -> (p op(square.filled.tiny) r = p op(square.filled.tiny) s), "refl"_b op(square.filled.tiny_l) beta :eq.triple "lu"_r^(-1) op(square.filled.tiny) beta op(square.filled.tiny) "lu"_s$.
]

#proof[
  略.
]

#lemma[
  對於任何 $a, b, c : A, p, q : a = b, r, s : b = c, alpha: p = q, beta: r = s$，我們有 $(alpha op(square.filled.tiny_r) r) op(square.filled.tiny) (q op(square.filled.tiny_l) beta) = (p op(square.filled.tiny_l) beta) op(square.filled.tiny) (alpha op(square.filled.tiny_r) s)$.
]

#proof[
  略.
]

#theorem[
  *Eckmann–Hilton*

  $
    (alpha, beta : op(Omega^2) (A, a)) -> (alpha op(square.filled.tiny) beta = beta op(square.filled.tiny) alpha)
  $
]

#proof[
  略.
]

#definition[
  *有點類型*

  設 $A: cal(U), a: A$. 序偶 $(A, a) : (A: cal(U)) times A$ 稱爲一個*有點類型*，$a$ 稱爲它的*基點*. 類型 $(A: cal(U)) times A$ 記爲 $cal(U)_circle.filled.small$.
]

#definition[
  *迴路空間*

  對於 $n: NN$，一個有點類型 $(A, a)$ 的 *$n$ 重迭代迴路空間* $op(Omega)^n (A, a)$ 遞歸地定義爲
  $
    op(Omega)^0 (A, a) :eq.triple (A, a)，
  $$
    op(Omega)^1 (A, a) :eq.triple ((a scripts(=)_A a), "refl"_a)，
  $$
    op(Omega)^(n+1) (A, a) :eq.triple op(Omega)^n (op(Omega) (A, a))，
  $
  它的一個項稱爲點 $a$ 的一個 *$n$ 維迴路*.
]

#convention[
  設 $op(Omega^(n))(A,a) eq.triple (B,b)$. 則 $x: op(Omega^(n))(A,a)$ 表示 $x: B$.
]

== *函數是函子*

#lemma[
  對於任何 $A, B : cal(U), f: A -> B, x, y : A$，都能構造函數 $op(bold("ap"_f)): (x scripts(=)_A y) -> (f(x) scripts(=)_B f(y)), op("ap"_f) ("refl"_x) eq.triple "refl"_(f(x))$.
]

#proof[
  第一種證明：設 $D: (x, y : A) -> (x scripts(=)_A y) -> cal(U), D(x, y, p) :eq.triple (f(x) scripts(=)_B f(y))$. 那麼我們有 $d :eq.triple (x: A) |-> "refl"_(f(x)) : (x: A) -> (f(x) scripts(=)_B f(y))$. 根據 $p$ 的道路歸納，我們得到函數 $op("ap"_f): (x scripts(=)_A y) -> (f(x) scripts(=)_B f(y))$. 根據恆等類型的計算規則，對於任何 $x: A$，有 $op("ap"_f) ("refl"_x) eq.triple "refl"_(f(x))$.

  第二種證明：爲了對任何 $p: x = y$ 定義 $op("ap"_f) (p)$，根據 $p$ 的道路歸納，只需要構造 $p$ 是 $"refl"_x$ 的情況. 在該情況下，我們定義 $op("ap"_f) ("refl"_x) :eq.triple "refl"_(f(x)) : f(x) = f(x)$.
  
]

#convention[
  我們將經常將 $op("ap"_f) (p)$ 簡寫爲 $f(p)$.
]

#lemma[
  對於任何函數 $f: A -> B, g: B -> C$ 和道路 $p: x scripts(=)_A y, q: y scripts(=)_A z$，我們有：

  $1.$ $op("ap"_f) (p op(square.filled.tiny) q) = op("ap"_f) (p) op(square.filled.tiny) op("ap"_f) (q)$；

  $2.$ $op("ap"_f) (p^(-1)) = (op("ap"_f) (p))^(-1)$；

  $3.$ $op("ap"_g) (op("ap"_f) (p)) = op("ap"_(g compose f)) (p)$；

  $4.$ $op("ap"_(op(id_A))) (p) = p$.
]

#proof[
  $1.$ 根據的道路歸納，只需要證明 $op("ap"_f) ("refl"_x op(square.filled.tiny) "refl"_x) = op("ap"_f) ("refl"_x) op(square.filled.tiny) op("ap"_f) ("refl"_x)$，這太簡單，遂略.

  $2.$ 根據道路歸納，只需要證明 $op("ap"_f) ("refl"_x^(-1)) = (op("ap"_f) ("refl"_x))^(-1)$，略.

  $3.$ 根據道路歸納，只需證明 $op("ap"_g) (op("ap"_f) ("refl"_x)) = op("ap"_(g compose f)) ("refl"_x)$，即 $op("ap"_g) ("refl"_(f(x))) = "refl"_(g compose f)$，略.

  $4.$ 根據道路歸納，只需證明 $op("ap")_(op("id")_A) ("refl"_x) = "refl"_x$，略.
]

== *類型族是纖維化*

#lemma[
  *傳送*

  設 $B: A -> cal(U), x, y : A$，則存在函數 $op(bold("transport")^B) ("_","_") : (x scripts(=)_A y) -> B(x) -> B(y), op(bold("transport")^B) ("refl"_x, "_") eq.triple op("id"_(B(x)))$.
]

#proof[
  第一種證明：設 $D: (x, y : A) -> (p: x = y) -> cal(U), D(x, y, p) :eq.triple B(x) -> B(y)$. 那麼我們有函數 $d :eq.triple (x: A) |-> op("id"_(B(x))) : D(x, x, "refl"_x)$. 根據道路歸納，對於任何 $x, y : A, p: x = y$，我們有函數 $op("ind"_(scripts(=)_A)) (D, d, x, y, p) : B(x) -> B(y)$. 於是我們可以定義，對於任何 $p: x = y$，函數 $op("transport"^B) (p, " _") :eq.triple op("ind"_(scripts(=)_A)) (D, d, x, y, p)$. 根據計算規則，$op("transport"^B) ("refl"_x, " _") eq.triple op("id"_(B(x)))$.

  第二種證明：根據道路歸納，只需假設 $p$ 是 $"refl"_x$. 在該情況下，對於任何 $b: B(x)$，我們定義 $op("transport"^B) ("refl"_x, b) :eq.triple b$.
]

#lemma[
  *道路提升*

  設 $P: A -> cal(U), x, y: A$. 則對於任何 $u: P(x), p: x = y$，我們有 $op("lift") (u, p) : (x, u) scripts(=)_((x: A) times P(x)) (y, op("transport"^P) (p, u)), op("lift") (u, "refl"_x) eq.triple "refl"_((x, u))$.
]

#proof[
  根據道路歸納，只需證明 $(x, u) = (x, op("id"_(P(x))) (u))$，略.
]

#lemma[
  *依賴映射*

  設 $B: A -> cal(U), f: (x: A) -> B(x), x, y : A$. 我們有映射 $op("apd"_f) : (p: x scripts(=)_A y) -> (op("transport"^B) (p, f(x)) scripts(=)_(B(y)) f(y)), op("apd"_f) ("refl"_x) :eq.triple "refl"_(f(x))$.
]

#proof[
  第一種證明：設 $D: (x, y : A) -> (x = y) -> cal(U), D(x, y, p) :eq.triple op("transport"^B) (p, f(x)) scripts(=)_(B(y)) f(y)$. 於是我們有函數 $d :eq.triple (x: A) |-> "refl"_(f(x)) : (x: A) -> D(x, x, "refl"_x)$. 根據道路歸納，對於任何 $x, y :A, p: x = y$，我們有函數 $op("ind"_(scripts(=)_A)) (D, d, x, y, p) : op("transport"^B) (p, f(x)) scripts(=)_(B(y)) f(y)$. 於是我們可以定義，對於任何 $p: x = y$，函數 $op("apd"_f) (p) :eq.triple op("ind"_(scripts(=)_A)) (D, d, x, y, p)$. 根據計算規則，$op("apd"_f) ("refl"_x) :eq.triple "refl"_(f(x))$.

  第二種證明：根據道路歸納，只需假設 $p$ 是 $"refl"_x$. 在該情況下，我們定義 $op("apd"_f) ("refl"_x) :eq.triple "refl"_(f(x)) : op("transport"^B) ("refl"_x, f(x)) scripts(=)_(B(x)) f(x)$.
]

#lemma[
  設 $B: A -> cal(U), B(x) :eq.triple B, x, y : A$. 則能構造函數 $op("transportconst"^B) ("_","_") : (p: x = y) -> b: B -> b = op("transport"^B) (p, b)$.
]

#proof[
  根據道路歸納，只需證明 $(b: B) -> b = op("transport"^B) ("refl"_x, b)$，即 $(b: B) -> b = b$. 顯然只需定義 $op("transportconst"^B) ("refl"_x, b) :eq.triple "refl"_b$.
]

#lemma[
  設 $f: A -> B, x, y : A$. 則對於任何道路 $p: x = y$，我們有類型爲 $op("ap"_f) (p) = op("transportconst"^B) (p, f(x)) op(square.filled.tiny) op("apd"_f) (p)$ 的道路.
]

#proof[
  根據道路歸納，只需證明 $op("ap"_f) ("refl"_x) = op("transportconst"^B) ("refl"_x, f(x)) op(square.filled.tiny) op("apd"_f) ("refl"_x)$，即 $"refl"_(f(x)) = "refl"_(f(x)) op(square.filled.tiny) "refl"_(f(x))$，這是顯然的.
]

#lemma[
  $(P: A -> cal(U)) -> (x, y : A) -> (p: x = y) -> (q: y = z) -> (u: P(x)) -> op("transport"^P) (q, op("transport"^P) (p, u)) = op("transport"^P) (p op(square.filled.tiny) q, u).$
]

#proof[
  略.
]

#lemma[
  $(f: A -> B) -> (P: B -> cal(U)) -> (x, y : A) -> (p: x = y) -> (u: P(f(x))) -> op("transport"^(P compose f)) (p, u) = op("transport"^P) (op("ap"_f) (p), u).$
]

#proof[
  略.
]

#lemma[

  $(P, Q : A -> cal(U)) -> (f: (x: A) -> P(x) -> Q(x)) -> (x, y : A) -> (p: x = y) -> (u: P(x)) -> op("transport"^Q) (p, f_x (u)) scripts(=)_(Q(y)) f_y (op("transport"^P) (p, u)).$
]

#proof[
  略.
]

== *同倫和等價*

#definition[
  *同倫*

  設 $P: A -> cal(U), f, g : (x: A) -> P(x)$. 從 $f$ 到 $g$ 的一個*同倫*定義爲一個類型爲 $(f op(~) g) :eq.triple (x: A) -> f(x) = g(x)$ 的函數.
]

#lemma[
  設 $f: A -> B$. 則 $(x: A) |-> "refl"_(f(x)) : f op(~) f$.
]

#proof[
  略.
]

#lemma[
  設 $P: A -> cal(U)$. 我們有：

  $1.$ $(f: (x: A) -> P(x)) -> (f op(~) f)$；

  $2.$ $(f, g : (x: A) -> P(x)) -> (f op(~) g) -> (g op(~) f)$；

  $3.$ $(f, g, h : (x: A) -> P(x)) -> (f op(~) g) -> (g op(~) h) -> (f op(~) h)$.
]

#proof[
  略.
]

#lemma[
  設 $f, g : A -> B, H: f op(~) g$. 則對於任何 $x, y : A, p: x = y$ 我們有 $H(x) op(square.filled.tiny) g(p) = f(p) op(square.filled.tiny) H(y)$，即下圖交換

  #align(
    center,
    commutative-diagram(
      node((0,0), $f(x)$), node((0,1), $f(y)$),
      node((1,0), $g(x)$), node((1,1), $g(y)$),
      arr((0,0), (1,0), $H(x)$, label-pos: right),
      arr((1,0), (1,1), $g(p)$, label-pos: right),
      arr((0,0), (0,1), $f(p)$),
      arr((0,1), (1,1), $H(y)$),
    )
  )
]

#proof[
  略.
]

#corollary[
  設 $f: A -> A, H: f op(~) op("id"_A)$. 則對於任何 $x: A$ 我們有 $H(f(x)) = f(H(x))$.
]

#proof[
  根據 $H$ 的自然性，我們有 $f(op(H) x) op(square.filled.tiny) op(H) x = H(op(f) x) op(square.filled.tiny) op(H) x$，即下圖交換

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(f) op(f) x$), node((0,1), $op(f) x$),
      node((1,0), $op(f) x$), node((1,1), $x$),
      arr((0,0), (1,0), $H(op(f) x)$, label-pos: right),
      arr((1,0), (1,1), $op(H) x$, label-pos: right),
      arr((0,0), (0,1), $f(op(H) x)$),
      arr((0,1), (1,1), $op(H) x$),
    )
  )

  我們可以用 $(op(H) x)^(-1)$ 加鬚來消除 $op(H) x$，得到 $f(op(H) x) = f(op(H) x) op(square.filled.tiny) op(H) x op(square.filled.tiny) (op(H) x)^(-1) = H(op(f) x) op(square.filled.tiny) op(H) x op(square.filled.tiny) (op(H) x)^(-1) = H(op(f) x)$.
]

#definition[
  *擬逆*

  對於一個函數 $f: A -> B$，它的一個*擬逆*是一個三元組 $(g, alpha, beta) : op(bold("qinv")) (f) :eq.triple (g: B -> A) times [(g compose f op(~) op("id"_A)) times (f compose g op(~) op("id"_B))]$.
]

#definition[
  *等價*

  對於任何函數 $f: A -> B$，定義 *$op("isequiv")$*$(f) :eq.triple [(g: B -> A) times (g compose f op(~) op("id"_A))] times [(h: B -> A) times (f compose h op(~) op("id"_B))]$，$(A$ *$tilde.eq$* $B) :eq.triple (f: A -> B) times op("isequiv") (f)$.
]

#lemma[
  $1.$ 對於任何 $f: A -> B$，存在函數 $op("qinv") (f) -> op("isequiv") (f)$；

  $2.$ 對於任何 $f: A -> B$，存在函數 $op("isequiv") (f) -> op("qinv") (f)$.
]

#proof[
  $1.$ 略.

  $2.$ 給定四元組 $(g, alpha, h, beta)： op("isequiv") (f)$，我們有 $alpha: (x: A) -> (g compose f) (x) = x, beta: (y: B) -> (f compose h) (y) = y$，那麼我們有同倫 $g compose beta^(-1) : (y: B) -> g(y) = (g compose f compose h) (y) eq.triple g op(~) (g compose f compose h)$ 和 $alpha compose h : (y: B) -> (g compose f compose h) (y) = h(y) eq.triple (g compose f compose h) op(~) h$. 於是我們可以定義同倫 $gamma :eq.triple (g compose beta^(-1)) op(square.filled.tiny) (alpha compose h) : g op(~) h eq.triple (y: B) -> g(y) = h(y)$. 那麼 $f compose gamma : (y: B) -> (f compose g) (y) = (f compose h) (y) eq.triple (f compose g) op(~) (f compose h)$. 於是有 $(f compose gamma) op(square.filled.tiny) beta : (f compose g) op(~) op("id"_B)$. 所以有 $(g, alpha, (f compose gamma) op(square.filled.tiny) beta) : op("qinv") (f)$.
]

#lemma[
  $1.$ 對於任何類型 $A: cal(U)$，我們有 $op("isequiv") (op("id"_A))$，即 $A tilde.eq A$；

  $2.$ 對於任何函數 $f: A -> B$ 使得 $op("isequiv") (f)$，即 $A tilde.eq B$，我們有一個函數 $f^(-1) : B -> A$ 使得 $op("isequiv") (f^(-1))$，即 $B tilde.eq A$；

  $3.$ 對於任何函數 $f: A -> B$ 使得 $op("isequiv") (f)$（即 $A tilde.eq B$）和 $g: B -> C$ 使得 $op("isequiv") (g)$（即 $B tilde.eq C$），我們有 $op("isequiv") (g compose f)$（即 $A tilde.eq C$）.
]

#proof[
  $1.$ 我們要證明對於任何類型 $A: cal(U)$ 有 $[(g: B -> A) times (g compose op("id"_A) op(~) op("id"_A))] times [(h: B -> A) times (op("id"_A) compose h op(~) op("id"_B))]$，略.

  $2.$ $f$ 的擬逆.

  $3.$ $f^(-1) compose g^(-1)$ 是 $g compose f$ 的一個擬逆.
]

== *$Sigma$-類型*

#theorem[
  設 $P: A -> cal(U)$，$w, w' : (x: A) times P(x)$.

  則我們有一個等價 $(w = w') tilde.eq (p: op("pr"_1) (w) = op("pr"_1) (w')) times (op("transport"^P) (p, op("pr"_2) (w)) = op("pr"_2) (w'))$.
]

#proof[
  略.
]

== *單元類型*

#theorem[
  $
    (x, y : bold(1)) -> ((x = y) tilde.eq bold(1)).
  $
]

#proof[
  根據單元類型和恆等類型的歸納原理，我們只需要證明 $(ast.small = ast.small) tilde.eq bold(1)$. 設函數 $f: (ast.small = ast.small) -> bold(1), x |-> ast.small$ 和 $g: bold(1) -> (ast.small = ast.small), x |-> "refl"_ast.small$. 那麼我們只需證明對於任何 $x: ast.small = ast.small$ 有 $(g compose f) (x) = op("id"_(ast.small = ast.small)) (x)$ 和對於任何 $x: bold(1)$ 有 $(f compose g) (x) = op("id"_(bold(1))) (x)$. 根據單元類型和恆等類型的歸納原理，我們只需要證明 $(g compose f) ("refl"_ast.small) = op("id"_(ast.small = ast.small)) ("refl"_ast.small)$ 和 $(f compose g) (ast.small) = op("id"_(bold(1))) (ast.small)$，略.
]

#theorem[
  $
    (x, y : bold(1)) -> (x = y).
  $
]

#proof[
  略.
]

== *$Pi$-類型*

#lemma[
  *happly*

  對於任何函數 $f, g : (x: A) -> B(x)$，我們有函數
  $
    op(bold("happly")) : (f = g) -> (x: A) -> (f(x) = g(x)),
  $$
    op(bold("happly")) ("refl"_f) :eq.triple (x: A) |-> "refl"_(f(x)).
  $
]

#proof[
  略.
]
== *宇宙和泛等公理*

#lemma[
  對於任何類型 $A, B : cal(U)$，我們有一個函數 $op(bold("idtoeqv")_(A, B)) : (A scripts(=)_cal(U) B) -> (A tilde.eq B)$.
]

#proof[
  函數 $op("transport"^(op("id"_cal(U)))) ("_", "_") : (A scripts(=)_cal(U) B) -> A -> B$. 我們要證明 $(p: A scripts(=)_cal(U) B) -> op("isequiv") (op("transport"^(op("id"_cal(U)))) (p, "_"))$. 根據 $p$ 的道路歸納，只需證明 $op("isequiv") (op("transport"^(op("id"_cal(U)))) ("refl"_A, "_"))$，即證明 $op("isequiv") (op("id"_A))$，略.

  定義 $op(bold("idtoeqv")_(A, B)) (p) :eq.triple (op("transport"^(op("id"_cal(U)))) (p, "_"), a) : A tilde.eq B$，其中 $a: op("isequiv") (op("transport"^(op("id"_cal(U)))) (p, "_"))$.
]

#lemma[
  $(op("id"_A), a) = op("idtoeqv"_(A,B)) ("refl"_A)$，其中 $a: op("isequiv") (op("id"_A))$.
]

#proof[
  略.
]

#lemma[
  對於任何 $x, y : A, p: x = y, B: A -> cal(U), u: B(x)$，我們有 $op("transport"^B) (p, u) = op("transport"^(op("id"_cal(U)))) (op("ap"_B) (p), u) = op(op("pr"_1) (op("idtoeqv") (op("ap"_B) (p)))) (u)$.
]

#proof[
  根據歸納原理，只需證明 $op("transport"^B) ("refl"_x, u) = op("transport"^(op("id"_cal(U)))) (op("ap"_B) ("refl"_x), u) = op(op("pr"_1) (op("idtoeqv") (op("ap"_B) ("refl"_x)))) (u)$，略.
]

#definition[
  *泛等公理*（不常用）

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash B: cal(U)_i$],
    prooftrees.bin(right_label: [$" "cal(U)_i"-UNIV"$])[$Gamma vdash op(bold("univalence")) (A,B) : op("isequiv") (op("idtoeqv"_(A,B)))$],
  )
]

#lemma[
  $(op("idtoeqv"_(A,B)), op("univalence") (A,B)) : (A scripts(=)_cal(U) B) tilde.eq (A tilde.eq B)$.
]

#proof[
  略.
]

#definition[
  *泛等公理*（常用）

  $1.$ 對於任何類型 $A, B : cal(U)$，我們有一個函數 $op(bold("ua")) : (A tilde.eq B) -> (A scripts(=)_cal(U) B)$；

  $2.$ 對於任何 $(f, a) : A tilde.eq B$，我們有 $op("idtoeqv"_(A,B)) (op(bold("ua")) (f, a)) = (f, a)$；

  $3.$ 對於任何 $p: A scripts(=)_cal(U) B$，我們有 $p = op(bold("ua")) (op("idtoeqv"_(A, B)) (p))$.
]

#lemma[
  $1.$ 對於任何類型 $A: cal(U)$，我們有 $"refl"_A = op("ua") (op("id"_A), a)$，其中 $a: op("isequiv") (op("id"_A))$；

  $2.$ 對於任何 $(f, a) : A tilde.eq B, (g, b) : B tilde.eq C$，我們有 $op("ua") (f, a) op(square.filled.tiny) op("ua") (g, b) = op("ua") (g compose f, c)$.

  $3.$ 對於任何 $(f, a) : A tilde.eq B$ 和它的一個擬逆 $(f^(-1), b)$，我們有 $(op("ua") (f, a))^(-1) = op("ua") (f^(-1), b)$.
]

#proof[
  略.
]

== *恆等類型*

#theorem[
  如果 $(f, a) : A tilde.eq B$，則對於任何 $x, x' : A$，函數 $op("ap"_f) : (x = x') -> (f(x) = f(x'))$ 也是一個等價.
]

#proof[
  我們想要構造一個四元組 $(g, gamma, h, delta) : op("isequiv") (op("ap"_f))$，即 $g: (f(x) = f(x')) -> (x = x'), gamma: (p: x = x') -> (g(op("ap"_f) (p)) = p), h: (f(x) = f(x')) -> (x = x'), delta: (q: f(x) = f(x')) -> (op("ap"_f) (g(q)))$.

  設 $(f^(-1), alpha, beta) : op("qinv") (f)$，即 $f^(-1) : B -> A, alpha: (x: A) -> (f^(-1)(f(x)) = x), beta: (y: B) -> (f(f^(-1) (y)) = y)$.
  
  那麼對於任何 $x, x' : A$，我們有 $op("ap"_(f^(-1))) : (f(x) = f(x')) -> (f^(-1)(f(x)) = f^(-1)(f(x')))$.
  
  於是對於任何 $p: x = x'$，我們有
  
  $alpha_x^(-1) op(square.filled.tiny) op("ap"_(f^(-1))) (op("ap"_f) (p)) op(square.filled.tiny) alpha_(x')$
  
  $= alpha_x^(-1) op(square.filled.tiny) op("ap"_(f^(-1) compose f)) (p) op(square.filled.tiny) alpha_(x')$
  
  $= op("ap"_(op("id"_A))) (p)$
  
  $= p$.
  
  且對於任何 $q: f(x) = f(x')$，我們有
  
  $op("ap"_f) (alpha_x^(-1) op(square.filled.tiny) op("ap"_(f^(-1))) (q) op(square.filled.tiny) alpha_(x'))$
  
  $= beta_(f(x))^(-1) op(square.filled.tiny) beta_(f(x)) op(square.filled.tiny) op("ap"_f) (alpha_x^(-1) op(square.filled.tiny) op("ap"_(f^(-1))) (q) op(square.filled.tiny) alpha_(x')) op(square.filled.tiny) beta_(f(x'))^(-1) op(square.filled.tiny) beta_(f(x'))$
  
  $= beta_(f(x))^(-1) op(square.filled.tiny)
  op("ap"_f) (
    op("ap"_f^(-1)) (
      op("ap"_f) (
        alpha_x^(-1) op(square.filled.tiny) op("ap"_(f^(-1))) (q) op(square.filled.tiny) alpha_(x')
      )
    )
  )
  op(square.filled.tiny) beta_(f(x'))$
  
  $= beta_(f(x))^(-1) op(square.filled.tiny)
  op("ap"_f) (alpha_x op(square.filled.tiny) alpha_x^(-1) op(square.filled.tiny) op("ap"_(f^(-1))) (q) op(square.filled.tiny) alpha_(x') op(square.filled.tiny) alpha_(x')^(-1))
  op(square.filled.tiny) beta_(f(x'))$
  
  $= beta_(f(x))^(-1) op(square.filled.tiny)
  op("ap"_f) (op("ap"_(f^(-1))) (q))
  op(square.filled.tiny) beta_(f(x'))$
  
  $= q$.
]

#lemma[
  對於任何 $a, x_1, x_2 : A$ 和 $p: x_1 = x_2$，我們有

  $1.$ $(q: a = x_1) -> op("transport"^(x |-> (a = x))) (p, q) = q op(square.filled.tiny) p$；

  $2.$ $(q: x_1 = a) -> op("transport"^(x |-> (x = a))) (p, q) = p^(-1) op(square.filled.tiny) q$；

  $3.$ $(q: x_1 = x_2) -> op("transport"^(x |-> (x = x))) (p, q) = p^(-1) op(square.filled.tiny) q op(square.filled.tiny) p$.
]

#proof[
  略.
]

== *自然數*

#definition[
  $op(bold("code"))$

  定義函數
  $
    op(bold("code")) : NN -> NN -> cal(U)，
  $
  模式匹配
  $
    op(bold("code")) (0, 0) :eq.triple bold(1)
  $$
    op(bold("code")) (op("succ") (m), 0) :eq.triple bold(0)
  $$
    op(bold("code")) (0, op("succ") (n)) :eq.triple bold(0)
  $$
    op(bold("code")) (op("succ") (m), op("succ") (n)) :eq.triple op(bold("code")) (m, n).
  $
]

#definition[
  $op(bold(r))$

  定義函數
  $
    op(bold(r)) : (n: NN) -> op("code") (n, n)
  $
  模式匹配
  $
    op(bold(r)) (0) :eq.triple ast.small
  $$
    op(bold(r)) (op("succ") (n)) :eq.triple op(bold(r)) (n).
  $
]

#theorem[
  對於任何 $m, n : NN$ 我們有 $(m = n) tilde.eq op("code") (m, n)$.
]

#proof[
  定義函數
  $
    op(bold("encode")) : (m, n : NN) -> (m = n) -> op("code") (m, n),
  $$
  op(bold("encode")) (m, n, p) :eq.triple op("transport"^(op("code") (m,"_"))) (p, op(r) (m))，
  $ 和函數 $
    op(bold("decode")) : (m, n : NN) -> op("code") (m, n) -> (m = n),
  $ 模式匹配 $
    op(bold("decode"))(0, 0, ast.small) :eq.triple "refl"_0
  $$
    op(bold("decode")) (op("succ") (m), 0, "_") :eq.triple op("ind"_bold(0)) ((x: bold(0)) |-> (m = n), "_")
  $$
    op(bold("decode")) (0, op("succ") (n), "_") :eq.triple op("ind"_bold(0)) ((x: bold(0)) |-> (m = n), "_")
  $$
    op(bold("decode")) (op("succ") (m), op("succ") (n), "_") :eq.triple op("ap"_op("succ")) compose op(bold("decode")) (m, n, "_").
  $

  接下來我們要證明對於任何 $m, n : NN$ 有 $op("encode") (m, n, "_")$ 和 $op("decode") (m, n, "_")$ 互爲擬逆.

  我們先證明對於任何 $p: m = n$ 有 $op("decode") (m, n, op("encode") (m, n, p)) = p$. 根據 $p$ 的道路歸納，只需證明 $op("decode") (m, m, op("encode") (m, m, "refl"_m)) = "refl"_m$，即 $op("decode") (m, m, r(m)) = "refl"_m$. 對 $m$ 使用歸納法，如果 $m eq.triple 0$，那麼 $op("decode") (0, 0, r(0)) = op("decode") (0, 0, ast.small) = "refl"_0$；設 $x: NN, y: op("decode") (x, x, r(x)) = "refl"_x$，則 $op("decode") (op("succ") (x), op("succ") (x), r(op("succ") (x))) = op("ap"_op("succ")) (op("decode") (x, x, r(x))) = op("ap"_op("succ")) ("refl"_x) = "refl"_(op("succ") (x))$.

  然後我們證明對於任何 $c: op("code") (m, n)$ 有 $op("encode") (m, n, op("decode") (m, n, c)) = c$. 我們對 $m, n$ 進行雙歸納. 如果都是 $0$，那麼 $op("encode") (0, 0, op("decode") (0, 0, c)) = op("encode") (0, 0, op("decode") (0, 0, ast.small)) = op("encode") (0, 0, "refl"_0) = r(0) = ast.small = c$；如果 $m$ 是 $0$ 且 $n$ 是一個後繼，或反之，那麼有 $c: bold(0)$；最後是兩個後繼的情況，根據歸納假設我們有
  $
    op("encode") (op("succ") (m), op("succ") (n), op("decode") (op("succ") (m), op("succ") (n), c))
  $$
    = op("encode") (op("succ") (m), op("succ") (n), op("ap"_op("succ")) (op("decode") (m, n, c)))
  $$
    = op("transport"^(op("code") (op("succ") (m),"_"))) (op("ap"_op("succ")) (op("decode") (m, n, c)), r(op("succ") (m)))
  $$
    = op("transport"^(op("code") (op("succ") (m), op("succ") ("_")))) (op("decode") (m, n, c), r(op("succ") (m)))
  $$
    = op("transport"^(op("code") (m, "_"))) (op("decode") (m, n, c), r(m))
  $$
    = op("encode") (m, n, op("decode") (m, n, c))
  $$
    = c
  $
]

#corollary[
  $1.$ 對於任何 $m: NN$，我們有 $op("encode") (op("succ") (m), 0, "_") : (op("succ") (m) = 0) -> bold(0)$；

  $2.$ 對於任何 $m, n : NN$，我們有 $op("encode") (op("succ") (m), op("succ") (n), op("decode") (op("succ") (m), op("succ") (n), "_")) : (op("succ") (m) = op("succ") (n)) -> (m = n)$.
]

#proof[
  略.
]

#pagebreak()

= *集合和邏輯*

== *集合和 $n$-類型*

#definition[
  *集合（$0$-類型）*

  設 $A: cal(U)$.
  $
    op(bold("isSet")) (A) :eq.triple (x, y : A) -> (p, q : x = y) -> (p = q).
  $
]

#definition[
  *$1$-類型*

  一個類型 $A$ 是一個 *$1$-類型* 如果 $(x, y : A) -> (p, q : x = y) -> (alpha, beta : p = q) -> (alpha = beta)$.
]

#lemma[
  如果 $A$ 是一個集合，則 $A$ 是一個 $1$-類型.
]

#proof[
  我們想證明 $[(x, y : A) -> (p, q : x = y) -> (p = q)] -> (x, y : A) -> (p, q : x = y) -> (alpha, beta : p = q) -> (alpha = beta)$.

  設 $f: op("isSet") (A)$. 那麼對於任何 $x, y : A$ 和 $p, q : x = y$ 我們有 $p = q$. 給定 $x, y$ 和 $p$，定義 $g: (q: x = y) -> (p = q), g :eq.triple f(x, y, p, "_")$. 那麼對於任何 $q, q' : x = y$ 和 $alpha: q = q'$，我們有 $op("apd"_g) (alpha) : op("transport"^(q |-> (p = q))) (alpha, g(q)) = g(q')$，也就有 $g(q) op(square.filled.tiny) alpha = g(q')$.

  因此對於任何 $x, y : A, p, q : x = y, alpha, beta : p = q$，我們有 $g(p) op(square.filled.tiny) alpha = g(q)$ 且 $g(p) op(square.filled.tiny) beta = g(q)$，也就有 $g(p) op(square.filled.tiny) alpha = g(p) op(square.filled.tiny) beta$，也就有 $alpha = beta$.
]

== *命題*

#definition[
  *命題（$-1$-類型）*

  設 $A: cal(U)$.
  $
    op(bold("isProp")) (A) :eq.triple (x, y : A) -> (x = y).
  $
]

#lemma[
  如果 $P, Q$ 是命題使得 $P -> Q$ 且 $Q -> P$，則 $P tilde.eq Q$.
]

#proof[
  略.
]

#lemma[
  如果 $P$ 是一個命題且 $x_0 : P$，則 $P tilde.eq bold(1)$.
]

#proof[
  略.
]

#lemma[
  每個命題都是一個集合.
]

#proof[
  我們想證明 $[(x, y : A) -> (x = y)] -> (x, y : A) -> (p, q : x = y) -> (p = q)$.

  設 $f: op("isProp") (A)$. 那麼對於任何 $x, y : A$ 我們有 $f(x, y) : x = y$. 給定 $x$，定義 $g: (y: A) -> x = y, g : eq.triple f(x, "_")$. 那麼對於任何 $y, z : A$ 和 $p: y = z$，我們有 $op("apd"_g) (p) : op("transport"^(y |-> x = y)) (p, g(y)) = g(z)$，也就有 $g(y) op(square.filled.tiny) p = g(z)$，也就有 $p = (g(y))^(-1) op(square.filled.tiny) g(z)$.

  因此對於任何 $x, y : A, p, q : x = y$，我們有 $p = (g(x))^(-1) op(square.filled.tiny) g(y) = q$.
]

== *子集*

#lemma[
  設 $P: A -> cal(U)$ 且對於任何 $x: A$，$P(x)$ 是一個命題. 則對於任何 $u, v : (x: A) times P(x)$，若 $op("pr"_1) (u) = op("pr"_1) (v)$，則有 $u = v$.
]

#proof[
  設 $p: op("pr"_1) (u) = op("pr"_1) (v)$. 則爲了證明 $u = v$，我們只需證明 $op("transport"^P) (p, op("pr"_2) (u)) = op("pr"_2) (v)$. 因爲 $op("transport"^P) (p, op("pr"_2) (u)), op("pr"_2) (v) : P(op("pr"_1) (v))$ 且該類型是一個命題，所以證畢.
]

#definition[
  *子類型，子集*

  設 $P: A -> cal(U)$ 是一個命題族（即每個 $P(x)$ 是一個命題）.

  $
    {x: A | P(x)} :eq.triple (x: A) times P(x)；
  $$
    a in {x: A | P(x)} :eq.triple P(a).
  $

  ${x: A | P(x)}$ 稱爲 $A$ 的一個*子類型*；如果 $A$ 是集合，則 ${x: A | P(x)}$ 稱爲 $A$ 的一個*子集*.
]

#definition[
  *$"Set"_cal(U)$*

  定義 $cal(U)$ 的一個“子宇宙”：
  $
    bold("Set")_cal(U) :eq.triple {A: cal(U) | op("isSet") (A)}.
  $
]

== *可縮性*

#definition[
  *可縮的*

  $
    op(bold("isContr")) (A) :eq.triple (a: A) times ((x: A) -> (a = x)).
  $
]

#pagebreak()

= *範疇論*

== *範疇和預範疇*

#definition[
  *預範疇*

  一個*預範疇* $A$ 系如下資料：

  $1.$ 一個類型 $A_0$，它的項稱爲*對象*；

  $2.$ 一個函數 $op("hom"_A) : A_0 -> A_0 -> "Set"$，集合 $op("hom"_A) (a, b)$ 的元素稱爲*態射*；

  $3.$ 一個函數 $op(1) : (a: A_0) -> op("hom"_A) (a, a)$，$op(1)_a$ 稱爲*恆等態射*；

  $4.$ 一個函數 $"_" compose "_" : op("hom"_A) (b, c) -> op("hom"_A) (a, b) -> op("hom"_A) (a, c)$ 稱爲*合成*；

  $5.$ 對於任何 $a, b : A_0$ 和 $f: op("hom"_A) (a, b)$，我們有 $f = op(1)_b compose f$ 且 $f = f compose op(1)_a$；

  $6.$ 對於任何 $a, b, c, d : A$ 和 $f: op("hom"_A) (a, b), g: op("hom"_A) (b, c), h: op("hom"_A) (c, d)$，我們有 $h compose (g compose f) = (h compose g) compose f$.
]