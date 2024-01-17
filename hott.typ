#import "template.typ": *
#import "typreset/lib.typ": font, thm-envs
#import "commute.typ": node, arr, commutative-diagram
#import "prooftrees/prooftrees.typ"
#import "prooftrees/internal.typ"
#import "@local/cetz:0.1.2"

#show: font.set-font.with(lang: "zh")

#let (theorem, definition, lemma, corollary, proof, proposition, example, convention, axiom, recall) = thm-envs.presets()
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
  *函數的合成*

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

  $2.$ 對於任何 $a, b, c : A, r, s : b = c$，我們可以構造函數 *$"_" op(square.filled.tiny_l) "_"$* $: (p: a = b) -> (r = s) -> (p op(square.filled.tiny) r = p op(square.filled.tiny) s), "refl"_b op(square.filled.tiny_l) beta :eq.triple "lu"_r^(-1) op(square.filled.tiny) beta op(square.filled.tiny) "lu"_s$.
]

#proof[
  略.
]

#lemma[
  *橫合成*

  對於任何 $a, b, c : A$，$p, q : a = b$，$r, s : b = c$，我們可以構造函數 $"_" op(square.filled.tiny) "_" : (p = q) -> (r = s) -> (p op(square.filled.tiny) r = q op(square.filled.tiny) s)$.
]

#proof[
  略.
]

#lemma[
  *剪鬚*

  $1.$ 對於任何 $a, b, c : A, p, q : a = b$，我們可以構造函數 $(r: b = c) -> (p op(square.filled.tiny) r = q op(square.filled.tiny) r) -> (p = q)$；

  $2.$ 對於任何 $a, b, c : A, r, s : b = c$，我們可以構造函數 $(p: a = b) -> (p op(square.filled.tiny) r = p op(square.filled.tiny) s) -> (r = s)$.
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
  對於任何 $A, B : cal(U), f: A -> B, x, y : A$，都能構造函數 $op(bold("ap")_f): (x scripts(=)_A y) -> (f(x) scripts(=)_B f(y)), op(bold("ap")_f) ("refl"_x) eq.triple "refl"_(f(x))$.
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

#definition[
  *纖維化*

  我們把類型族 $P: A -> cal(U)$ 視爲一個*纖維化*，$A$ 稱爲它的*底空間*，$P(x)$ 稱爲 $x$ 上的*纖維*，$(x: A) times P(x)$ 稱爲它的*全空間*，如果存在函數 $f: (x: A) -> P(x)$，則稱該函數爲 $P$ 的一個*截面*.

  有時也稱全空間爲 $A$ 上的*纖維化*.
]

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

  設 $P: A -> cal(U), x, y: A$. 則對於任何 $u: P(x), p: x = y$，我們有 $op(bold("lift")) (u, p) : (x, u) scripts(=)_((x: A) times P(x)) (y, op("transport"^P) (p, u)), op(bold("lift")) (u, "refl"_x) eq.triple "refl"_((x, u))$.
]

#proof[
  根據道路歸納，只需證明 $(x, u) = (x, op("id"_(P(x))) (u))$，略.
]

#lemma[
  *依賴映射*

  設 $B: A -> cal(U), f: (x: A) -> B(x), x, y : A$. 我們有映射 $op(bold("apd")_f) : (p: x scripts(=)_A y) -> (op("transport"^B) (p, f(x)) scripts(=)_(B(y)) f(y)), op(bold("apd")_f) ("refl"_x) :eq.triple "refl"_(f(x))$.
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

  設 $P: A -> cal(U), f, g : (x: A) -> P(x)$. 從 $f$ 到 $g$ 的一個*同倫*定義爲一個類型爲 $(f tilde g) :eq.triple (x: A) -> f(x) = g(x)$ 的函數.
]

#lemma[
  設 $f: A -> B$. 則 $(x: A) |-> "refl"_(f(x)) : f tilde f$.
]

#proof[
  略.
]

#lemma[
  設 $P: A -> cal(U)$. 我們有：

  $1.$ $(f: (x: A) -> P(x)) -> (f tilde f)$；

  $2.$ $(f, g : (x: A) -> P(x)) -> (f tilde g) -> (g tilde f)$；

  $3.$ $(f, g, h : (x: A) -> P(x)) -> (f tilde g) -> (g tilde h) -> (f tilde h)$.
]

#proof[
  略.
]

#lemma[
  設 $f, g : A -> B, H: f tilde g$. 則對於任何 $x, y : A, p: x = y$ 我們有 $H(x) op(square.filled.tiny) g(p) = f(p) op(square.filled.tiny) H(y)$，即下圖交換

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
  設 $f: A -> A, H: f tilde op("id"_A)$. 則對於任何 $x: A$ 我們有 $H(f(x)) = f(H(x))$.
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

  對於一個函數 $f: A -> B$，它的一個*擬逆*是一個三元組 $(g, alpha, beta) : op(bold("qinv")) (f) :eq.triple (g: B -> A) times [(g compose f tilde op("id"_A)) times (f compose g tilde op("id"_B))]$.
]

#definition[
  *等價*

  對於任何函數 $f: A -> B$，定義 *$op("isequiv")$*$(f) :eq.triple [(g: B -> A) times (g compose f tilde op("id"_A))] times [(h: B -> A) times (f compose h tilde op("id"_B))]$，$(A$ *$tilde.eq$* $B) :eq.triple (f: A -> B) times op("isequiv") (f)$.
]

#lemma[
  $1.$ 對於任何 $f: A -> B$，存在函數 $op("qinv") (f) -> op("isequiv") (f)$；

  $2.$ 對於任何 $f: A -> B$，存在函數 $op("isequiv") (f) -> op("qinv") (f)$.
]

#proof[
  $1.$ 略.

  $2.$ 給定四元組 $(g, alpha, h, beta)： op("isequiv") (f)$，我們有 $alpha: (x: A) -> (g compose f) (x) = x, beta: (y: B) -> (f compose h) (y) = y$，那麼我們有同倫 $g compose beta^(-1) : (y: B) -> g(y) = (g compose f compose h) (y) eq.triple g tilde (g compose f compose h)$ 和 $alpha compose h : (y: B) -> (g compose f compose h) (y) = h(y) eq.triple (g compose f compose h) tilde h$. 於是我們可以定義同倫 $gamma :eq.triple (g compose beta^(-1)) op(square.filled.tiny) (alpha compose h) : g tilde h eq.triple (y: B) -> g(y) = h(y)$. 那麼 $f compose gamma : (y: B) -> (f compose g) (y) = (f compose h) (y) eq.triple (f compose g) tilde (f compose h)$. 於是有 $(f compose gamma) op(square.filled.tiny) beta : (f compose g) tilde op("id"_B)$. 所以有 $(g, alpha, (f compose gamma) op(square.filled.tiny) beta) : op("qinv") (f)$.
]

#lemma[
  $1.$ 對於任何類型 $A: cal(U)$，我們有 $op("isequiv") (op("id"_A))$，即 $A tilde.eq A$；

  $2.$ 對於任何函數 $f: A -> B$ 使得 $op("isequiv") (f)$，即 $A tilde.eq B$，我們有一個函數 $f^(-1) : B -> A$ 使得 $op("isequiv") (f^(-1))$，即 $B tilde.eq A$；

  $3.$ 對於任何函數 $f: A -> B$ 使得 $op("isequiv") (f)$（即 $A tilde.eq B$）和 $g: B -> C$ 使得 $op("isequiv") (g)$（即 $B tilde.eq C$），我們有 $op("isequiv") (g compose f)$（即 $A tilde.eq C$）.
]

#proof[
  $1.$ 我們要證明對於任何類型 $A: cal(U)$ 有 $[(g: B -> A) times (g compose op("id"_A) tilde op("id"_A))] times [(h: B -> A) times (op("id"_A) compose h tilde op("id"_B))]$，略.

  $2.$ $f$ 的擬逆.

  $3.$ $f^(-1) compose g^(-1)$ 是 $g compose f$ 的一個擬逆.
]

== *$Sigma$-類型*

#theorem[
  設 $B: A -> cal(U)$，$w, w' : (x: A) times B(x)$.

  則我們有一個等價 $(w = w') tilde.eq (p: op("pr"_1) (w) = op("pr"_1) (w')) times (op("transport"^B) (p, op("pr"_2) (w)) = op("pr"_2) (w'))$.
]

#proof[
  略.
]

#corollary[
  設 $B: A -> cal(U)$. 則對於任何 $w : (x : A) times B(x)$，我們有 $w = angle.l op("pr"_1) (w), op("pr"_2) (w) angle.r$.
]

#proof[
  略.
]

#lemma[
  設 $B: A -> cal(U)$，$C: (x: A) times (B(x) -> cal(U))$. 則我們有 $[(x: A) times (y: B(x)) times C(angle.l x,y angle.r)] tilde.eq [(p: (x: A) times B(x)) times C(p)]$.
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
    op(bold("happly")) (f,g) : (f = g) -> (x: A) -> (f(x) = g(x)),
  $$
    op(bold("happly")) (f,g,"refl"_f) :eq.triple (x: A) |-> "refl"_(f(x)).
  $
]

#proof[
  略.
]

#lemma[
  給定類型 $X$，一個路徑 $p : x_1 scripts(=)_X x_2$，類型族 $A,B : X -> cal(U)$，一個函數 $f : A(x_1) -> B(x_1)$. 則我們有：
  $
    op("transport"^(A -> B)) (p, f)
    scripts(=)_(A(x_2) -> B(x_2))
    x |-> op("transport"^B) (p, f(op("transport"^A) (p^(-1), x))).
  $
]

#proof[
  根據 $p$ 的道路歸納，我們只需證明 $op("transport"^(A -> B)) ("refl"_(x_1), f) scripts(=)_(A(x_1) -> B(x_1)) x |-> op("transport"^B) ("refl"_(x_1), f(op("transport"^A) ("refl"_(x_1), x)))$，即 $f scripts(=)_(A(x_1) -> B(x_1)) x |-> f(x)$，證畢.
]

== *宇宙和泛等公理*

#lemma[
  對於任何類型 $A, B : cal(U)$，我們有一個函數 $op(bold("idtoeqv")_(A, B)) : (A scripts(=)_cal(U) B) -> (A tilde.eq B)$.
]

#proof[
  函數 $op("transport"^op("id"_cal(U))) ("_", "_") : (A scripts(=)_cal(U) B) -> A -> B$. 我們要證明 $(p: A scripts(=)_cal(U) B) -> op("isequiv") (op("transport"^op("id"_cal(U))) (p, "_"))$. 根據 $p$ 的道路歸納，只需證明 $op("isequiv") (op("transport"^op("id"_cal(U))) ("refl"_A, "_"))$，即證明 $op("isequiv") (op("id"_A))$，略.

  定義 $op(bold("idtoeqv")_(A, B)) (p) :eq.triple (op("transport"^op("id"_cal(U))) (p, "_"), a) : A tilde.eq B$，其中 $a: op("isequiv") (op("transport"^op("id"_cal(U))) (p, "_"))$.
]

#lemma[
  $(op("id"_A), a) = op("idtoeqv"_(A,B)) ("refl"_A)$，其中 $a: op("isequiv") (op("id"_A))$.
]

#proof[
  略.
]

#lemma[
  對於任何 $x, y : A, p: x = y, B: A -> cal(U), u: B(x)$，我們有 $op("transport"^B) (p, u) = op("transport"^op("id"_cal(U))) (op("ap"_B) (p), u) = op(op("pr"_1) (op("idtoeqv") (op("ap"_B) (p)))) (u)$.
]

#proof[
  根據歸納原理，只需證明 $op("transport"^B) ("refl"_x, u) = op("transport"^op("id"_cal(U))) (op("ap"_B) ("refl"_x), u) = op(op("pr"_1) (op("idtoeqv") (op("ap"_B) ("refl"_x)))) (u)$，略.
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

== *餘積*

#definition[
  $op(bold("code"))$（“固定 $a_0 : A$”的版本）

  給定 $A,B : cal(U)$，$a_0 : A$.

  定義函數
  $
    op(bold("code")) : A + B -> cal(U)，
  $
  模式匹配
  $
    op(bold("code")) (op("inl") ("_")) :eq.triple a_0 = "_" : A -> cal(U)
  $$
    op(bold("code")) (op("inr") ("_")) :eq.triple b |-> bold(0) : B -> cal(U).
  $
]

#theorem[
  對於任何 $x : A + B$，我們有 $(op("inl") (a_0) = x) tilde.eq op("code") (x)$.
]

#proof[
  定義函數
  $
    op(bold("encode")) : (x : A + B) -> (op("inl") (a_0) = x) -> op("code") (x),
  $$
    op(bold("encode")) (x, p) :eq.triple op("transport"^(op("code"))) (p, "refl"_(a_0)).
  $ 和函數 $
    op(bold("decode")) : (x : A + B) -> op("code") (x) -> (op("inl") (a_0) = x),
  $ 模式匹配 $
    op(bold("decode"))(op("inl") (a), c) :eq.triple op("ap"_(op("inl")) (c))
  $$
    op(bold("decode"))(op("inr") (b), c) :eq.triple op("ind"_bold(0)) ((x: bold(0)) |-> (op("inl") (a_0) = op("inr") (b)), c)
  $

  接下來我們需要證明對於任何 $x : A + B$ 有 $op("encode") (x, "_")$ 和 $op("decode") (x, "_")$ 互爲擬逆.

  在其中一個方向，我們要證明對於任何 $p : op("inl") (a_0) = x$ 有 $op("decode") (x, op("encode") (x, p)) = p$. 根據 $p$ 的道路歸納，我們只需證明 $x eq.triple op("inl") (a_0)$，$p eq.triple "refl"_(op("inl") (a_0))$ 的情況：
  $
    op("decode") (op("inl") (a_0), op("encode") (op("inl") (a_0), "refl"_(op("inl") (a_0))))
  $$
    eq.triple op("decode") (op("inl") (a_0), op("transport"^(op("code"))) ("refl"_(op("inl") (a_0)), "refl"_(a_0)))
  $$
    eq.triple op("decode") (op("inl") (a_0), "refl"_(a_0))
  $$
    eq.triple op("ap"_(op("inl"))) ("refl"_(a_0)) 
  $$
    eq.triple "refl"_(op("inl") (a_0))
  $$
    eq.triple p.
  $

  在另一個方向，我們要證明對於任何 $c : op("code") (x)$ 有 $op("encode") (x, op("decode") (x, c)) = c$：

  當 $x eq.triple op("inl") (a)$ 時，$c : a_0 = a$：
  $
    op("encode") (op("inl") (a), op("decode") (op("inl") (a), c))
  $$
    eq.triple op("encode") (op("inl") (a), op("ap"_(op("inl")) (c)))
  $$
    eq.triple op("transport"^op("code")) (op("ap"_(op("inl")) (c)), "refl"_(a_0))
  $$
    eq.triple op("transport"^(a |-> (a_0 = a))) (c, "refl"_(a_0))
  $$
    eq.triple "refl"_(a_0) op(square.filled.tiny) c
  $$
    eq.triple c.
  $

  當 $x eq.triple op("inr") (b)$ 時，$c : bold(0)$，略.
]

#corollary[
  $
    op("encode") (op("inl") (a), "_") : (op("inl") (a_0) = op("inl") (a)) -> (a_0 = a)；
  $$
    op("encode") (op("inr") (b), "_") : (op("inl") (a_0) = op("inr") (b)) ->bold(0).
  $
]

#proof[
  略.
]

#lemma[
  $bold(2) tilde.eq bold(1) + bold(1)$.
]

#proof[
  略.
]

#corollary[
  $" "0_bold(2) != 1_bold(2)$.
]

#proof[
  略.
]

#definition[
  *$(A + B)$*

  給定一個類型 $X$，類型族 $A,B : X -> cal(U)$，定義類型族：
  $
    bold((A + B)) : X -> cal(U), bold((A + B)) (x) :eq.triple A(x) + B(x).
  $
]

#lemma[
  給定一個類型 $X$，一個道路 $p : x_1 scripts(=)_X x_2$，類型族 $A,B : X -> cal(U)$，則我們有：

  $
    op("transport"^(A + B)) (p, op("inl") (a)) = op("inl") (op("transport"^A) (p,a))；
  $$
    op("transport"^(A + B)) (p, op("inr") (b)) = op("inr") (op("transport"^A) (p,b)).
  $
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
    op(bold("decode")) (op("succ") (m), 0, c) :eq.triple op("ind"_bold(0)) ((x: bold(0)) |-> (m = n), c)
  $$
    op(bold("decode")) (0, op("succ") (n), c) :eq.triple op("ind"_bold(0)) ((x: bold(0)) |-> (m = n), c)
  $$
    op(bold("decode")) (op("succ") (m), op("succ") (n), c) :eq.triple op("ap"_op("succ")) compose op(bold("decode")) (m, n, c).
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

== *泛性質*

#theorem[
  設 $A : X -> cal(U)$，$P : (x : X) -> A(x) -> cal(U)$. 則有等價：

  $
    [(x : X) -> (a : A(x)) times P(x,a)] tilde.eq [(g : (x : X) -> A(x)) times ((x : X) -> P(x, g(x)))]
  $
]

#proof[
  定義函數 $phi : [(x : X) -> (a : A(x)) times P(x,a)] -> [(g : (x : X) -> A(x)) times ((x : X) -> P(x, g(x)))],$ $phi(f) :eq.triple angle.l x |-> op("pr"_1) (f(x)), x |-> op("pr"_2) (f(x)) angle.r$ 和 $psi : [(g : (x : X) -> A(x)) times ((x : X) -> P(x, g(x)))] -> [(x : X) -> (a : A(x)) times P(x,a)],$ $psi(angle.l g,h angle.r) :eq.triple x |-> angle.l g(x), h(x) angle.r$.

  剩餘證明略.
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

#example[
  類型 $bold(1)$ 是一個集合.
]

#example[
  類型 $bold(0)$ 是一個集合.
]

#example[
  自然數類型 $NN$ 是一個集合.
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

#example[
  宇宙 $cal(U)$ 不是一個集合.
]

#proof[
  設 $f : bold(2) -> bold(2), f(0_bold(2)) :eq.triple 0_bold(2), f(1_bold(2)) :eq.triple 0_bold(2)$. 顯然 $f$ 是一個等價. 因此，根據泛等，由 $f$ 可以導出一個道路 $p : A = A$.

  如果 $p = "refl"_A$，那麼有 $f = op("id"_A)$，矛盾，證畢.
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
  如果 $P$ 是一個命題且 $x_0 : P$，則 $P tilde.eq bold(1)$.
]

#proof[
  略.
]

#lemma[
  如果 $P$ 和 $Q$ 是命題，且有 $P -> Q$ 和 $Q -> P$，則我們有 $P tilde.eq Q$.
]

#proof[
  設 $f: P -> Q$，$g: Q -> P$. 那麼由於 $P$ 是命題，則對於任何 $x: P$ 我們有 $g(f(x)) = x$. 同理，對於任何 $y: Q$ 我們有 $f(g(y)) = y$. 因此 $f$ 和 $g$ 互爲擬逆.
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

== *命題截斷*

#definition[
  *命題截斷（$-1$-截斷）*

  *命題截斷*系如下資料：

  $1.$ 類型形成器：$|| "_" || : cal(U) -> cal(U)$；

  $2.$ 構造子 $1$：$| "_" | : A -> ||A||$；

  $3.$ 構造子 $2$：對於任何 $x, y : ||A||$，我們有 $x = y$；

  $4.$ 消除器：如果有 $op("isProp") (B)$，則有 $op("rec"_(|| "_" ||)) : (A -> B) -> ||A|| -> B$；

  $5.$ 計算規則：$op("rec"_(|| "_" ||)) (f) (|a|) :eq.triple f(a)$
]

#definition[
  *傳統邏輯記號*

  給定類型 $A$ 和 $B$.

  $
    A "和" B "是邏輯等價的"（A "iff" B） :eq.triple (A -> B) times (B -> A)
  $

  給定命題 $P$ 和 $Q$.

  $
    tack.b :eq.triple bold(1)
  $$
    tack.t :eq.triple bold(0)
  $$
    P and Q :eq.triple P times Q
  $$
    P => Q :eq.triple P -> Q
  $$
    P <=> Q :eq.triple P = Q
  $$
    not P :eq.triple P -> bold(0)
  $$
    P or Q :eq.triple ||P + Q||
  $$
    forall (x: A). P(x) :eq.triple (x: A) -> P(x)
  $$
    exists (x: A). P(x) :eq.triple ||(x: A) times P(x)||
  $$
    {x: A | P(x)} sect {x: A | Q(x)} :eq.triple {x: A | P(x) and Q(x)}
  $$
    {x: A | P(x)} union {x: A | Q(x)} :eq.triple {x: A | P(x) or Q(x)}
  $$
    A backslash {x: A | P(x)} :eq.triple {x: A | not P(x)}
  $
]

== *可縮性*

#definition[
  *可縮的*

  $
    op(bold("isContr")) (A) :eq.triple (a: A) times ((x: A) -> (a = x)).
  $
]

#lemma[
  對於任何類型 $A$，以下類型是邏輯等價的：

  $1.$ $op("isContr") (A)$；

  $2.$ $A times op("isProp") (A)$；

  $3.$ $A tilde.eq bold(1)$.
]

#proof[
  略.
]

#lemma[
  對於任何類型 $A$，類型 $op("isContr") (A)$ 是命題.
]

#proof[
  略.
]

#lemma[
  如果類型 $A$ 等價於 $B$ 且 $A$ 可縮，則 $B$ 可縮.
]

#proof[
  略.
]

#definition[
  *收縮*，*截面*，*收縮核*

  稱函數 $r: A -> B$ 是一個*收縮*，如果存在一個函數 $s: B -> A$，稱爲它的一個*截面*，和一個同倫 $r compose s tilde op("id"_B)$. 我們稱 $B$ 爲 $A$ 的一個*收縮核*.
]

#lemma[
  如果 $B$ 是 $A$ 的一個收縮核，且 $A$ 是可縮的，則 $B$ 是可縮的.
]

#proof[
  令 $r: A -> B$ 是一個收縮，$s: B -> A$ 是它的一個截面，$epsilon : r compose s tilde op("id"_B)$，$a_0 : A$，$"contr"_(s(b)) : a_0 = s(b)$，$b_0 :eq.triple r(a_0), b : B$.

  那麼我們有 $r("contr"_(s(b))) op(square.filled.tiny) epsilon(b) : b_0 = b$，證畢.
]

#lemma[
  對於任何類型 $A$ 和 $a: A$，類型 $(x: A) times (a = x)$ 是可縮的.
]

#proof[
  我們要證明 $(angle.l x,p angle.r : (x: A) times (a = x)) -> angle.l a,"refl"_a angle.r = angle.l x,p angle.r$，略.
]

#lemma[
  設 $B: A -> cal(U)$. 則有：

  $1.$ $[(x: A) -> op("isContr") (B(x))] -> [((x: A) times B(x)) tilde.eq A]$；

  $2.$ $(a: A) times [((x: A) -> (a = x)) -> (((x: A) times B(x)) tilde.eq B(a))]$.
]

#proof[
  略.
]

#pagebreak()

= *等價*

== *半伴隨等價*

#recall[
  對於任何函數 $f: A -> B$，定義 *$op("isequiv")$*$(f) :eq.triple [(g: B -> A) times (op(g) op(f) tilde op("id"_A))] times [(h: B -> A) times (op(f) op(h) tilde op("id"_B))]$，$(A$ *$tilde.eq$* $B) :eq.triple (f: A -> B) times op("isequiv") (f)$.

  對於一個函數 $f: A -> B$，它的一個*擬逆*是一個三元組 $(g, alpha, beta) : op(bold("qinv")) (f) :eq.triple (g: B -> A) times (op(g) op(f) tilde op("id"_A)) times (op(f) op(g) tilde op("id"_B))$.
]

#definition[
  *半伴隨等價*

  $
    op(bold("ishae")) (f) :eq.triple
    (g: B -> A) times (eta : op(g) op(f) tilde op("id"_A)) times (epsilon : op(f) op(g) tilde op("id"_B)) times
    (op(f) op(eta) tilde op(epsilon) op(f))；
  $$
    op(bold("ishae")') (f) :eq.triple
    (g: B -> A) times (eta : op(g) op(f) tilde op("id"_A)) times (epsilon : op(f) op(g) tilde op("id"_B)) times
    (op(g) op(epsilon) tilde op(eta) op(g)).
  $
]

#lemma[
  $op("ishae") (f)$ 和 $op("ishae"') (f)$ 是邏輯等價的.
]

#proof[
  我們先證明 $op("ishae") (f) -> op("ishae"') (f)$.

  設 $(g, eta, epsilon, tau) : op("ishae") (f)$. 我們要構造一個四元組 $(g', eta', epsilon', tau') : op("ishae"') (f)$. 設 $g' :eq.triple g$，$eta' :eq.triple eta$，$epsilon' :eq.triple epsilon$.
  
  由 $op(g) op(epsilon)$ 的自然性，我們有路徑的交換圖如下：

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(g) op(f) op(g) op(f) op(g) y$), node((0,1), $op(g) op(f) op(g) y$),
      node((1,0), $op(g) op(f) op(g) y$), node((1,1), $op(g) y$),
      arr((0,0), (0,1), $op(g) op(f) op(g) op(epsilon) y$),
      arr((1,0), (1,1), $op(g) op(epsilon) y$, label-pos:right),
      arr((0,0), (1,0), $op(g) op(epsilon) op(f) op(g) y$, label-pos: right),
      arr((0,1), (1,1), $op(g) op(epsilon) y$),
    )
  )

  從而有：

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(g) op(f) op(g) op(f) op(g) y$), node((0,1), $op(g) op(f) op(g) y$),
      node((1,0), $op(g) op(f) op(g) y$), node((1,1), $op(g) y$),
      arr((0,0), (0,1), $op(g) op(f) op(g) op(epsilon) y$),
      arr((1,0), (1,1), $op(g) op(epsilon) y$, label-pos:right),
      arr((0,0), (1,0), $op(g) op(f) op(eta) op(g) y$, label-pos: right),
      arr((0,1), (1,1), $op(g) op(epsilon) y$),
    )
  )

  從而有：

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(g) op(f) op(g) op(f) op(g) y$), node((0,1), $op(g) op(f) op(g) y$),
      node((1,0), $op(g) op(f) op(g) y$), node((1,1), $op(g) y$),
      arr((0,0), (0,1), $op(g) op(f) op(g) op(epsilon) y$),
      arr((1,0), (1,1), $op(g) op(epsilon) y$, label-pos:right),
      arr((0,0), (1,0), $op(eta) op(g) op(f) op(g) y$, label-pos: right),
      arr((0,1), (1,1), $op(eta) op(g) y$),
    )
  )

  根據 $eta$ 的自然性，我們有：

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(g) op(f) op(g) op(f) op(g) y$), node((0,1), $op(g) op(f) op(g) y$),
      node((1,0), $op(g) op(f) op(g) y$), node((1,1), $op(g) y$),
      arr((0,0), (0,1), $op(g) op(f) op(g) op(epsilon) y$),
      arr((1,0), (1,1), $op(g) op(epsilon) y$, label-pos:right),
      arr((0,0), (1,0), $op(eta) op(g) op(f) op(g) y$, label-pos: right),
      arr((0,1), (1,1), $op(g) op(epsilon) y$),
    )
  )

  所以我們有 $op(g) op(epsilon) y = op(eta) op(g) y$，證畢.

  反方向類似，略.
]

#theorem[
  對於任何 $f: A -> B$，我們有 $op("ishae") (f)$ iff $op("qinv") (f)$.
]

#proof[
  正方向顯然，我們來證明反方向.

  設 $(g, eta, epsilon) : op("qinv") (f)$. 我們要構造一個四元組 $(g', eta', epsilon', tau) : op("ishae") (f)$. 設 $g' :eq.triple g$，$eta' :eq.triple eta$. 我們要構造合適的 $epsilon'$的定義，使得對於任何 $a: A$ 有 $op(f) op(eta) a = op(epsilon') op(f) a$.

  根據 $epsilon$ 的自然性，我們有如下交換圖：

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(f) op(g) op(f) op(g) op(f) a$), node((0,1), $op(f) op(g) op(f) a$),
      node((1,0), $op(f) op(g) op(f) a$), node((1,1), $op(f) a$),
      arr((0,1), (1,1), $op(epsilon) op(f) a$),
      arr((0,0), (1,0), $op(epsilon) op(f) op(g) op(f) a$, label-pos: right),
      arr((1,0), (1,1), $op(f) op(eta) a$, label-pos: right),
      arr((0,0), (0,1), $op(f) op(g) op(f) op(eta) a$),
    )
  )

  所以有 $(op(f) op(g) op(f) op(eta) a) op(square.filled.tiny) (op(epsilon) op(f) a) = (op(epsilon) op(f) op(g) op(f) a) op(square.filled.tiny) (op(f) op(eta) a)$，於是有 $(op(epsilon) op(f) op(g) op(f) a)^(-1) op(square.filled.tiny) (op(f) op(eta) op(g) op(f) a) op(square.filled.tiny) (op(epsilon) op(f) a) = op(f) op(eta) a$.

  於是我們可以定義 $epsilon' b :eq.triple (op(epsilon) op(f) op(g) b)^(-1) op(square.filled.tiny) (op(f) op(eta) op(g) b) op(square.filled.tiny) (op(epsilon) b)$，證畢.
]

#definition[
  *同倫纖維*

  一個函數 $f: A -> B$ 在一個點 $y: B$ 的一個*同倫纖維*定義爲：
  $
    op(bold("fib")_f) (y) :eq.triple (x: A) times (f(x) = y).
  $
]

#lemma[
  對於任何 $f: A -> B, y:B$ 和 $(x,p), (x',p') : op("fib"_y)$. 我們有 $((x,p) = (x',p')) tilde.eq ((gamma : x = x') times (p = f(gamma) op(square.filled.tiny) p'))$.
]

#proof[
  略.
]

#theorem[
  如果 $f: A -> B$ 是一個半伴隨等價，則對於任何 $y: B$，同倫纖維 $op("fib"_f) (y)$ 是可縮的.
]

#proof[
  設 $(g, eta, epsilon, tau) : op("ishae") (f)$，$y: B$. 那麼有 $(op(g) y, op(epsilon) y) : op("fib"_f) (y)$. 設 $(x,p) : op("fib"_f)$，我們要構造從 $(op(g) y, op(epsilon) y)$ 到 $(x,p)$ 的一條道路. 我們只需給出路徑 $gamma: op(g) y = x$ 使得 $op(epsilon) y = f(gamma) op(square.filled.tiny) p$.

  根據 $epsilon$ 的自然性，我們有：

  #align(
    center,
    commutative-diagram(
      node((1,1), $y$),
      node((0,1), $op(f) op(g) y$),
      node((1,0), $op(f) x$),
      node((0,0), $op(f) op(g) op(f) x$),
      arr((0,1), (1,1), $op(epsilon) y$),
      arr((1,0), (1,1), $p$, label-pos: right),
      arr((0,0), (1,0), $op(epsilon) op(f) x$, label-pos: right),
      arr((0,0), (0,1), $op(f) op(g) p$),
    )
  )

  也就有：

  #align(
    center,
    commutative-diagram(
      node((1,1), $y$),
      node((0,1), $op(f) op(g) y$),
      node((1,0), $op(f) x$),
      node((0,0), $op(f) op(g) op(f) x$),
      arr((0,1), (1,1), $op(epsilon) y$),
      arr((1,0), (1,1), $p$, label-pos: right),
      arr((0,0), (1,0), $op(f) op(eta) x$, label-pos: right),
      arr((0,0), (0,1), $op(f) op(g) p$),
    )
  )

  令 $gamma :eq.triple (op(g) p)^(-1)$，證畢.
]

#definition[
  *左逆*和*右逆*

  給定 $f: A -> B$，我們定義 $f$ 的*左逆*和*右逆*的類型爲
  $
    op(bold("linv")) (f) :eq.triple (g: B -> A) times (op(g) op(f) tilde op("id"_A))；
  $$
    op(bold("rinv")) (f) :eq.triple (g: B -> A) times (op(f) op(g) tilde op("id"_B)).
  $
]

#lemma[
  如果 $f: A -> B$ 有一個擬逆 $g: B -> A$，那麼函數 $(f compose "_") : (C -> A) -> (C -> B)$ 和 $("_" compose f) : (B -> C) -> (A -> C)$ 也有擬逆.
]

#proof[
  $(g compose "_") : (C -> B) -> (C -> A)$；$("_" compose g) : (A -> C) -> (B -> C)$.

  $(f compose "_") compose (g compose "_") eq.triple f compose g compose "_"$；$("_" compose g) compose ("_" compose f) eq.triple "_" compose f compose g$.
]

#definition[
  給定 $f: A -> B$，$angle.l g,eta angle.r : op("linv") (f)$，$angle.l g,epsilon angle.r : op("rinv") (f)$. 我們定義：

  $
    op(bold("lcoh")_f) (angle.l g,eta angle.r) :eq.triple (epsilon : f compose g tilde op("id"_B)) times (op(g) op(epsilon) tilde op(eta) op(g))；
  $$
    op(bold("rcoh")_f) (angle.l g,epsilon angle.r) :eq.triple (eta : g compose f tilde op("id"_A)) times (op(f) op(eta) tilde op(epsilon) op(f)).
  $
]

#lemma[
  對於任何 $f: A -> B$，$angle.l g,eta angle.r : op("linv") (f)$，$angle.l g,epsilon angle.r : op("rinv") (f)$，我們有：

  $
    op("lcoh")_f (angle.l g,eta angle.r) tilde.eq (y: B) -> [angle.l op(f) op(g) y, op(eta) op(g) y angle.r = angle.l y, "refl"_(op(g) y) angle.r]；
  $$
    op("rcoh")_f (angle.l g,epsilon angle.r) tilde.eq (x: A) -> [angle.l op(g) op(f) x, op(epsilon) op(f) x angle.r = angle.l x, "refl"_(op(f) x) angle.r].
  $
]

#proof[
  略.
]

#lemma[
  如果 $f : A -> B$ 是一個半伴隨等價，則對於任何 $angle.l g,epsilon angle.r : op("rinv") (f)$，我們有 $op("rcoh")_f (angle.l g,epsilon angle.r)$ 是可縮的.
]

#proof[
  我們只需證明對於任何 $x : A$，$angle.l op(g) op(f) x, op(epsilon) op(f) x angle.r = angle.l x, "refl"_(op(f) x) angle.r$ 是可縮的.

  我們已經知道 $op("fib"_f) (op(f) x)$ 是可縮的，又因爲可縮空間的道路空間是可縮的，證畢.
]

== *雙可逆映射*

#definition[
  *雙可逆映射*
  
  我們將之前定義的 $op("isequiv")$ 重命名爲 $op(bold("biinv"))$：
  $
    op(bold("biinv")) (f) :eq.triple op("linv") times op("rinv").
  $
]

#theorem[
  對於任何 $f: A -> B$，我們有 $op("biinv") (f)$ iff $op("ishae") (f)$.
]

#proof[
  略.
]

== *可縮纖維*

#definition[
  *可縮映射*

  設 $f: A -> B$. 我們定義：
  $
    op(bold("isContr")) (f) :eq.triple (y: B) -> op("isContr") (op("fib"_f) (y)).
  $
]

#theorem[
  對於任何 $f: A -> B$，我們有 $op("ishae") (f)$ iff $op("isContr") (f)$.
]

#proof[
  正方向我們已經證明過了，現在我們來證明反方向.

  設 $P: op("isContr") (f)$ $eq.triple$ $(y: B) -> op("isContr") (op("fib"_f) (y))$ $eq.triple$ $(y: B) -> [a: op("fib"_f) (y)] times [(b: op("fib"_f) (y)) -> (a = b)]$ $eq.triple$ $(y: B) -> [a: (x: A) times (f(x) = y)] times [(b: (x: A) times (f(x) = y)) -> (a = b)]$. 設函數 $g: B -> A, op(g) y :eq.triple op("pr"_1) op("pr"_1) op(P) y$，函數 $epsilon : op(f) op(g) tilde op("id"_B), op(epsilon) y :eq.triple op("pr"_2) op("pr"_1) op(P) y$，函數 $alpha : (y: B) -> [(b: (x: A) times (f(x) = y)) -> ((op("pr"_1) op(P) y) = b)], op(alpha) y :eq.triple op("pr"_2) op(P) y$.

  我們要構造四元組 $angle.l g', epsilon', eta, tau angle.r : op("ishae") (f)$. 令 $g' :eq.triple g$，$epsilon' :eq.triple epsilon$.

  還剩 $eta$ 和 $tau$ 需要構造，這其實相當於構造 $op("rcoh"_f) (g, epsilon)$ 的一個項，也就相當於構造 $(x: A) -> [angle.l op(g) op(f) x, op(epsilon) op(f) x angle.r = angle.l x, "refl"_(op(f) x) angle.r]$ 的一個項，略.
]

#theorem[
  對於任何 $f: A -> B$，我們有 $op("qinv") (f)$ iff $op("isContr") (f)$ iff $op("ishae") (f)$ iff $op("biinv") (f)$.
]

== *閉包性質*

#definition[
  *收縮核*

  稱函數 $g: A -> B$ 是函數 $f: X -> Y$ 的一個*收縮核*，如果：
  
  $1.$ 存在如下一個圖：

  #align(
    center,
    commutative-diagram(
      node((0,0), $A$), node((0,1), $X$), node((0,2), $A$),
      node((1,0), $B$), node((1,1), $Y$), node((1,2), $B$),
      arr((0,0), (1,0), $g$, label-pos: right),
      arr((0,1), (1,1), $f$, label-pos: right),
      arr((0,2), (1,2), $g$),
      arr((0,0), (0,1), $s$, label-pos: right), arr((0,1), (0,2), $r$, label-pos: right),
      arr((1,0), (1,1), $s'$), arr((1,1), (1,2), $r'$),
      arr((0,0), (0,2), $op("id"_A)$, curve: 15deg),
      arr((1,0), (1,2), $op("id"_B)$, label-pos:right, curve: -15deg),
    )
  )

  使得有如下存在：

  (i) 一個同倫 $R : r compose s tilde op("id"_A)$；

  (ii) 一個同倫 $R' : r' compose s' tilde op("id"_B)$；

  (iii) 一個同倫 $L : f compose s tilde s' compose g$；

  (iv) 一個同倫 $K : g compose r tilde r' compose f$.

  $2.$ 對於任何 $a: A$，我們有一條道路 $H(a)$ 見證下圖的交換：

  #align(
    center,
    commutative-diagram(
      node((0,0), $op(g) op(r) op(s) a$),
      node((1,0), $op(g) a$),
      node((0,1), $op(r') op(f) op(s) a$),
      node((1,1), $op(r') op(s') op(g) a$),
      arr((0,0), (1,0), $op(g) op(R) a$, label-pos: right, "nat"),
      arr((1,0), (1,1), $(op(R') op(g) a)^(-1)$, label-pos: right, "nat"),
      arr((0,0), (0,1), $op(K) op(s) a$, "nat"),
      arr((0,1), (1,1), $op(r') op(L) a$, "nat"),
    )
  )
]

#recall[
  *纖維化*

  我們把類型族 $P: A -> cal(U)$ 視爲一個*纖維化*，$A$ 稱爲它的*底空間*，$P(x)$ 稱爲 $x$ 上的*纖維*，$(x: A) times P(x)$ 稱爲它的*全空間*，如果存在函數 $f: (x: A) -> P(x)$，則稱該函數爲 $P$ 的一個*截面*.

  有時也稱全空間爲 $A$ 上的*纖維化*.
]

#definition[
  *逐纖維變換*

  給定 $P,Q : A -> cal(U)$，我們稱一個函數 $f: (x: A) -> P(x) -> Q(x)$ 爲一個*逐纖維變換*.
]

#definition[
  $op(bold("total"))$

  給定 $P,Q : A -> cal(U)$ 和一個逐纖維變換 $f: (x: A) -> P(x) -> Q(x)$，我們定義函數

  $
    op(bold("total")) (f) :eq.triple (w: (x: A) times P(x)) |-> angle.l op("pr"_1) w, f(op("pr"_1) w, op("pr"_2) w) angle.r : [(x: A) times P(x)] -> (x: A) times Q(x).
  $
]

#theorem[
  設 $f: (x: A) -> P(x) -> Q(x)$ 是一個逐纖維變換，$x: A$，$v: Q(x)$. 那麼我們有一個雙可逆映射
  $
    op("fib"_(op("total") (f))) (angle.l x,v angle.r) tilde.eq op("fib"_(f(x))) (v).
  $
]

#proof[
  略.
]

#definition[
  *逐纖維等價*

  我們稱一個逐纖維變換 $f: (x: A) -> P(x) -> Q(x)$ 是一個*逐纖維等價*，如果 $(x: A) -> op("ishae") (f(x))$.
]

#theorem[
  設 $f: (x: A) -> P(x) -> Q(x)$ 是一個逐纖維變換. 那麼，“$f$ 是一個逐纖維等價” iff “$op("total") (f)$ 是一個雙可逆映射”.
]

#proof[
  $f$ 是一個逐纖維等價

  iff $(x: A) -> op("ishae") (f(x))$

  iff $(x: A) -> op("isContr") (f(x))$

  iff $(x: A) -> (v: Q(x)) -> op("isContr") (op("fib"_(f(x))) (v))$

  iff $(w: (x: A) times Q(x)) -> op("isContr") (op("fib"_(op("total") (f))) (w))$

  iff $op("isContr") (op("total") (f))$

  iff $op("total") (f)$ 是一個雙可逆映射.
]

== *對象分類器*

#lemma[
  設 $B: A -> cal(U)$，$a: A$，$op("pr"_1) : ((x: A) times B(x)) -> A$ 是投影函數. 則我們有一個雙可逆映射 $op("fib"_op("pr"_1)) (a) tilde.eq B(a)$.
]

#proof[
  略.
]

== *函數外延性*

#definition[
  *弱函數外延性原理（WFE）*

  *弱函數外延性原理*斷言：對於任何 $P: A -> cal(U)$，存在一個函數
  $
    [(x: A) -> op("isContr") (P(x))] -> op("isContr") [(x: A) -> P(x)].
  $
]

#lemma[
  設有類型 $A, B, X :cal(U)$ 和一個雙可逆映射 $e eq.triple angle.l f_e, alpha angle.r : A tilde.eq B$. 那麼存在一個雙可逆映射 $f_e compose "_" : (X -> A) tilde.eq (X -> B)$.
]

#proof[
  根據泛等，我們可以令 $e = op("idtoeqv") (p)$ 其中 $p: A = B$. 根據 $p$ 的道路歸納，我們只需假設 $p eq.triple "refl"_A$，那麼我們有 $e = op("id"_A)$. 剩餘證明略.
]

#corollary[
  設 $B: A -> cal(U)$，$(x: A) -> op("isContr") (B(x))$. 那麼我們有：

  $1.$ 投影 $op("pr"_1) : ((x: A) -> B(x)) -> A$ 是一個雙可逆映射；

  $2.$ 存在一個雙可逆映射 $op("pr"_1) compose "_" : [A -> ((x: A) times B(x))] tilde.eq (A -> A)$.
]

#proof[
  $1.$ 對於任何 $x: A$，我們有一個雙可逆映射 $op("fib"_op("pr"_1)) (x) tilde.eq B(x)$. 因爲 $B(x)$ 是可縮的，所以 $op("fib"_op("pr"_1)) (x)$ 是可縮的，所以 $op("pr"_1)$ 是可縮的，所以 $op("pr"_1)$ 是一個雙可逆映射.

  $2.$ 略.
]

#theorem[
  設 $B: A -> cal(U)$，$(x: A) -> op("isContr") (B(x))$，$alpha :eq.triple op("pr"_1) compose "_" : [A -> ((x: A) times B(x))] tilde.eq (A -> A)$. 那麼我們有：

  $1.$ $(x: A) -> B(x)$ 是 $op("fib"_alpha) (op("id"_A))$ 的一個收縮核；

  $2.$ $(x: A) -> B(x)$ 是可縮的（*弱函數外延性原理*）.
]

#proof[
  $1.$ 定義函數
  $phi :$
  $[(x : A) -> B(x)] -> op("fib"_alpha) (op("id"_A))$
  $eq.triple$
  $[(x : A) -> B(x)] -> [(g : A -> ((x: A) times B(x))) times (op("pr"_1) op(g) = op("id"_A))],$
  $phi(f)$
  $:eq.triple$
  $angle.l x |-> angle.l x,f(x) angle.r, "refl"_op("id"_A) angle.r$
  和
  $psi :$
  $op("fib"_alpha) (op("id"_A)) -> (x: A) -> B(x)$
  $eq.triple$
  $[(g : A -> ((x: A) times B(x))) times (op("pr"_1) op(g) = op("id"_A))] -> (x: A) -> B(x),$
  $psi(angle.l g, p angle.r)$
  $:eq.triple$
  $(x: A) |-> op("transport"^B) (op("happly") (p,x), op("pr"_2) op(g) x)$.

  顯然，$op(psi) op(phi) tilde op("id"_((x : A) -> B(x)))$.

  $2.$ 我們只需證明 $op("fib"_alpha) (op("id"_A))$ 是可縮的，而這可以通過證明 $alpha$ 是可縮的來證明，略.
]

#lemma[
  設 $f : A -> B$. 如果 $A,B$ 是可縮的，那麼 $f$ 是一個雙可逆映射.
]

#proof[
  設 $alpha : op("isContr") (A)$，$beta : op("isContr") (B)$，$a :eq.triple op("pr"_1) (alpha)$，$b :eq.triple op("pr"_1) (beta)$.
  
  那麼有 $p : b = f(a)$，對於任何 $y : B$ 有 $q_y :eq.triple op((op("pr"_2) op(beta))) y : b = y$
  
  我們要證明對於任何 $y : B$，$op("fib"_f) (y)$ 是可縮的.
  
  現在讓我們固定 $y : B$. 定義 $p_y :eq.triple p^(-1) op(square.filled.tiny) q_y : f(a) = y$. 因此 $angle.l a, p_y angle.r : op("fib"_f) (y)$.

  我們只需證明對於任何 $angle.l a', p' angle.r : op("fib"_f) (y)$ 有 $k : a = a'$ 和 $op("transport"^(op("fib"_f) (y))) (k, p_y)  = p'$.

  我們有 $op((op("pr"_2) op(alpha))) a' : a = a'$.

  根據道路歸納，我們只需要證明 $op("transport"^(op("fib"_f) (y))) ("refl"_a, p_y)  = p'$，即 $p_y = p'$.

  根據道路歸納，只需證明 $p_(f(a)) = p'$，即 $"refl"_(f(a)) = "refl"_(f(a))$.
]

#theorem[
  *函數外延性原理*

  對於任何 $B : A -> cal(U)$，$f : (x : A) -> B(x)$，$g : (x : A) -> B(x)$，我們有如下結論：
  
  函數
  $
    op("happly") (f,g) : (f = g) -> [(x : A) -> f(x) = g(x)]
  $
  是一個雙可逆映射.
]

#proof[
  我們只需證明 $op("happly") (f, "_") : (g : (x : A) -> B(x)) -> (f = g) -> (f tilde g)$ 是一個逐纖維等價，而這只需要證明 $op("total") (op("happly") (f, "_")) : [(g : (x : A) -> B(x)) times (f = g)] -> (g : (x : A) -> B(x)) times (f tilde g)$ 是一個雙可逆映射. 我們已經知道 $(g : (x : A) -> B(x)) times (f = g)$ 是可縮的，所以只需要證明 $(g : (x : A) -> B(x)) times (f tilde g)$ 是可縮的.

  我們有 $(g : (x : A) -> B(x)) times (f tilde g)$ 是 $(x : A) -> (u : B(x)) times (f(x) = u)$ 的一個收縮核，所以只需證明 $(x : A) -> (u : B(x)) times (f(x) = u)$ 是可縮的.

  根據 WFE，我們只需證明對於任何 $x : A$ 有 $(u : B(x)) times (f(x) = u)$ 是可縮的，證畢.
]

#corollary[
  $op(bold("funext"))$

  對於任何 $B : A -> cal(U)$，$f : (x : A) -> B(x)$，$g : (x : A) -> B(x)$，函數 $op("happly") (f,g) : (f = g) -> [(x : A) -> f(x) = g(x)]$ 有一個擬逆：

  $
    op(bold("funext")) : [(x : A) -> f(x) = g(x)] -> (f = g).
  $
]

#proof[
  略.
]

#lemma[
  對於任何類型 $A$，我們有 $op("isProp") (A)$ 和 $op("isSet") (A)$ 是命題.
]

#proof[
  $op("funext")$.
]

#lemma[
  $op("isProp") (A) tilde.eq (A -> op("isContr") (A))$.
]

#proof[
  我們只需證明 $op("isProp") (A)$ iff $(A -> op("isContr") (A))$，略.
]

#lemma[
  如果 $f : A -> B$ 有一個擬逆，那麼 $op("linv") (f)$ 和 $op("rinv") (f)$ 是可縮的.
]

#proof[
  根據函數外延性，我們有 $op("linv") (f) tilde.eq (g : B -> A) times (op(g) op(f) = op("id"_A))$，即 $op("linv") (f) tilde.eq op("fib"_("_" compose f)) (op("id"_A))$. 因爲 $op("fib"_("_" compose f)) (op("id"_A))$ 是可縮的，所以 $op("linv") (f)$ 是可縮的.

  類似地，可以證明 $op("rinv") (f)$ 是可縮的.
]

#theorem[
  對於任何 $f: A -> B$，$op("ishae") (f)$ 是一個命題.
]

#proof[
  我們只需假設 $f$ 是一個半伴隨等價，並證明 $op("ishae") (f)$ 是可縮的，即證明 $(g: B -> A) times (epsilon : op(f) op(g) tilde op("id"_B)) times (eta : op(g) op(f) tilde op("id"_A)) times (op(f) op(eta) tilde op(epsilon) op(f))$ 是可縮的，即證明 $(u : (g : B -> A) times (op(f) op(g) tilde op("id"_B))) times (eta : op((op("pr"_1) u)) op(f) tilde op("id"_A)) times (op(f) op(eta) tilde op((op("pr"_2) u)) op(f))$ 是可縮的，即證明 $(u : op("rinv") (f)) times op("rcoh") (angle.l op("pr"_1) (u), op("pr"_2) (u) angle.r)$ 是可縮的. 剩餘證明略.
]

#theorem[
  對於任何 $f: A -> B$，$op("biinv") (f)$ 是一個命題.
]

#proof[
  略.
]

#lemma[
  設 $A$ 是類型，$B : A -> cal(U)$ 且對於任何 $x : A$ 有 $B(x)$ 是一個命題. 則 $(x : A) -> B(x)$ 是一個命題.
]

#proof[
  $op("funext")$.
]

#theorem[
  對於任何 $f: A -> B$，$op("isContr") (f)$ 是一個命題.
]

#proof[
  略.
]

#theorem[
  對於任何 $f: A -> B$，我們有 $op("isContr") (f) tilde.eq op("ishae") (f) tilde.eq op("biinv") (f)$.
]

#proof[
  略.
]

#recall[
  *半伴隨等價*

  $
    op(bold("ishae")) (f) :eq.triple
    (g: B -> A) times (eta : op(g) op(f) tilde op("id"_A)) times (epsilon : op(f) op(g) tilde op("id"_B)) times
    (op(f) op(eta) tilde op(epsilon) op(f)).
  $
]

#convention[
  *等價*

  對於任何函數 $f: A -> B$，我們定義 $op(bold("isequiv")) (f) :eq.triple op("ishae") (f)$.
]

#lemma[
  對於任何函數 $f, g : A -> B$，有 $(f = g) -> (op("isequiv") (f) = op("equiv") (g))$.
]

#proof[
  略.
]

#convention[
  對於任何等價 $f$，以後如無必要，我們不區分 $f$ 和 $angle.l f,e angle.r$（其中 $e : op("isequiv") (f)$）.
]

#definition[
  *$(A -> B)$*

  給定類型 $X$，類型族 $A,B : X -> cal(U)$. 定義函數：
  
  $
    bold((A -> B)) : X -> cal(U), bold((A -> B)) (x) :eq.triple A(x) -> B(x).
  $
]

#theorem[
  *$not "DNE"_infinity$*
  $
    not ((A : cal(U)) -> not not A -> A)
  $
]

#proof[
  我們只需假設 $f : (A : cal(U)) -> not not A -> A$，並構造 $bold(0)$ 的一個項.

  設 $e : bold(2) tilde.eq bold(2), e (1_bold(2)) :eq.triple 0_bold(2), e (0_bold(2)) :eq.triple 1_bold(2)$ 是一個等價. 設 $p :eq.triple op("ua") (e) : bold(2) = bold(2)$.

  那麼我們有 $f(bold(2)) : not not bold(2) -> bold(2)$ 和
  $
    op("apd"_f) (p) : op("transport"^(A |-> not not A -> A)) (p, f(bold(2))) = f(bold(2)).
  $

  因此對於任何 $u : not not bold(2)$，我們有 $op("happly") (op("apd"_f) (p), u) : op("transport"^(A |-> not not A -> A)) (p, f(bold(2))) (u) = f(bold(2)) (u)$.

  那麼對於任何 $u : not not bold(2)$，我們有 $op("transport"^(A |-> not not A -> A)) (p, f(bold(2))) (u) = op("transport"^op("id"_cal(U))) (p, f(bold(2)) (op("transport"^(A |-> not not A)) (p^(-1), u)))$.

  根據 $op("funext")$，對於任何 $u,v : not not bold(2)$ 有 $u = v$. 因此我們有 $op("transport"^(A |-> not not A)) (p^(-1), u) = u$. 所以我們有 $op("transport"^op("id"_cal(U))) (op("ua") (e), f(bold(2)) (u)) = f(bold(2))(u)$.

  根據泛等，我們有
  $
    e(f(bold(2)) (u)) = f(bold(2))(u).
  $

  又因爲我們可以證明 $(x : bold(2)) -> not (e(x) = x)$，所以推出矛盾，證畢.
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

#definition[
  *同構*

  一個態射 $f : op("hom"_A) (a,b)$ 是一個*同構*，如果存在一個態射 $g : op("hom"_A) (b,a)$ 使得 $g compose f = 1_a$ 且 $f compose g = 1_b$.

  $
    op(bold("isIso")) (f) :eq.triple (g : op("hom"_A) (b,a)) times (g compose f = 1_a) times (f compose g = 1_b)，
  $

  $
    a bold(tilde.equiv) b :eq.triple (f : op("hom"_A) (a,b)) times op("isIso") (f).
  $
]

#lemma[
  對於任何態射 $f : op("hom"_A) (a,b)$，$op("isIso") (f)$ 是一個命題. 因此 $a tilde.equiv b$ 是一個集合.
]

#proof[
  只需證明 $g = g'$，略.

  我們以後將同構 $f : a tilde.equiv b$ 的*逆*記作 $bold(f^(-1))$.
]

#lemma[
  $op(bold("idtoiso"))$

  如果 $A$ 是一個預範疇且 $a,b$ 是它的對象，則有 $op(bold("idtoiso")_(a,b)) : (a = b) -> (a tilde.equiv b)$.
]

#proof[
  略.
]

#lemma[
  設 $A$ 是類型，$B : A -> cal(U)$ 且對於任何 $x : A$ 有 $B(x)$ 是一個集合. 則 $(x : A) -> B(x)$ 是一個集合.
]

#proof[
  $op("funext")$.
]

#example[
  預範疇 $cal(bold("Set"))$

  $1.$ 對象類型爲 $"Set"$；

  $2.$ $op("hom"_(cal(bold("Set")))) (a,b) :eq.triple a -> b$；

  $3.$ $1_a :eq.triple op("id"_a)$；

  $4.$ 態射合成定義爲函數的合成.
]

#definition[
  *範疇*

  稱一個預範疇 $A$ 是一個*範疇*，如果對於它的任何對象 $a,b$ 有 $op("idtoiso"_(a,b))$ 是一個等價.
]

#example[
  $cal("Set")$ 是一個範疇.
]

#proof[
  $op("ua")$.
]

#lemma[
  在一個範疇中，所有對象組成的類型是一個 $1$-類型.
]

#proof[
  只需證明 $a = b$ 是集合，略.
]