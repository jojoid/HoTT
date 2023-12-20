#import "template.typ": *
#import "typreset/lib.typ": font, thm-envs
#import "commute.typ": node, arr, commutative-diagram
#import "prooftrees/prooftrees.typ"
#import "prooftrees/internal.typ"
#import "@local/cetz:0.1.2"

#show: font.set-font.with(lang: "zh")

#let (theorem, definition, lemma, corollary, proof, proposition, example, convention) = thm-envs.presets()
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

== *依賴函數類型*

#definition[
  *依賴函數類型*

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

== *依賴序偶類型*

#definition[
  *依賴序偶類型*

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

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: A vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash b: B[a slash x]$],
    prooftrees.tri(right_label: $" "Sigma"-INTRO"$)[$Gamma vdash (a, b): (x: A) times B$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: A vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : A$],
      prooftrees.axi[$Gamma vdash b_1 eq.triple b_2 : B[a slash x]$],
    prooftrees.tri(right_label: $" "Sigma"-INTRO-EQ"$)[$Gamma vdash (a_1, b_1) eq.triple (a_2, b_2) : (x: A) times B$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (x: A) times B vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A, y: B vdash g: C[(x, y) slash z]$],
      prooftrees.axi[$Gamma vdash p: (x: A) times B$],
    prooftrees.tri(right_label: $" "Sigma"-ELIM"$)[$Gamma vdash op("ind")_((x: A) times B)(z.C, x.y.g, p): C[p slash z]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (x: A) times B vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A, y: B vdash g: C[(x, y) slash z]$],
      prooftrees.axi[$Gamma vdash p_1 eq.triple p_2 : (x: A) times B$],
    prooftrees.tri(right_label: $" "Sigma"-ELIM-EQ"$)[$Gamma vdash op("ind")_((x: A) times B)(z.C, x.y.g, p_1) eq.triple op("ind")_((x: A) times B)(z.C, x.y.g, p_2) : C[p_1 slash z] eq.triple C[p_2 slash z]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (x: A) times B vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A, y: B vdash g: C[(x, y) slash z]$],
      prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash b: B[a slash x]$],
    prooftrees.quart(right_label: $" "Sigma"-COMP"$)[$Gamma vdash op("ind")_((x: A) times B)(z.C, x.y.g, (a, b)) eq.triple g[a, b slash x, y] : C[p slash z]$],
  )
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

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.tri(right_label: [$" "+"-INTRO"_1$])[$Gamma vdash op("inl")(a): A + B$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash B: cal(U)_i$],
      prooftrees.axi[$Gamma vdash b: B$],
    prooftrees.tri(right_label: [$" "+"-INTRO"_2$])[$Gamma vdash op("inr")(b): A + B$],
  )

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

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (A + B) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A vdash c: C[op("inl")(x) slash z]$],
      prooftrees.axi[$Gamma, y: B vdash d: C[op("inr")(y) slash z]$],
      prooftrees.axi[$Gamma vdash e: (A + B)$],
    prooftrees.quart(right_label: [$" "+"-ELIM"$])[$Gamma vdash op("ind")_(A + B)(z.C, x.c, y.d, e): C[e slash z]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (A + B) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A vdash c: C[op("inl")(x) slash z]$],
      prooftrees.axi[$Gamma, y: B vdash d: C[op("inr")(y) slash z]$],
      prooftrees.axi[$Gamma vdash e_1 eq.triple e_2 : (A + B)$],
    prooftrees.quart(right_label: [$" "+"-ELIM-EQ"$])[$Gamma vdash op("ind")_(A + B)(z.C, x.c, y.d, e_1) eq.triple op("ind")_(A + B)(z.C, x.c, y.d, e_2) : C[e_1 slash z] eq.triple C[e_2 slash z]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (A + B) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A vdash c: C[op("inl")(x) slash z]$],
      prooftrees.axi[$Gamma, y: B vdash d: C[op("inr")(y) slash z]$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.quart(right_label: [$" "+"-COMP"_1$])[$Gamma vdash op("ind")_(A + B)(z.C, x.c, y.d, op("inl")(a)) eq.triple c[a slash x] : C[op("inl")(a) slash z]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, z: (A + B) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, x: A vdash c: C[op("inl")(x) slash z]$],
      prooftrees.axi[$Gamma, y: B vdash d: C[op("inr")(y) slash z]$],
      prooftrees.axi[$Gamma vdash b: B$],
    prooftrees.quart(right_label: [$" "+"-COMP"_2$])[$Gamma vdash op("ind")_(A + B)(z.C, x.c, y.d, op("inr")(b)) eq.triple d[b slash y] : C[op("inr")(b) slash z]$],
  )
]

== *空類型 $0$*

#definition[
  *空類型 $bold(0)$*

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "bold(0)"-FORM"$])[$Gamma vdash bold(0): cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(0) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a: bold(0)$],
    prooftrees.bin(right_label: [$" "bold(0)"-ELIM"$])[$Gamma vdash op("ind")_(bold(0))(x.C, a): C[a slash x]$],
  )

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

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "bold(1)"-INTRO"$])[$Gamma vdash ast.small: bold(1)$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(1) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c: C[ast.small slash x]$],
      prooftrees.axi[$Gamma vdash a: bold(1)$],
    prooftrees.tri(right_label: [$" "bold(1)"-ELIM"$])[$Gamma vdash op("ind")_(bold(1))(x.C, c, a): C[a slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(1) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c: C[ast.small slash x]$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : bold(1)$],
    prooftrees.tri(right_label: [$" "bold(1)"-ELIM-EQ"$])[$Gamma vdash op("ind")_(bold(1))(x.C, c, a_1) eq.triple op("ind")_(bold(1))(x.C, c, a_2) : C[a_1 slash x] eq.triple C[a_2 slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: bold(1) vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c: C[ast.small slash x]$],
    prooftrees.bin(right_label: [$" "bold(1)"-COMP"$])[$Gamma vdash op("ind")_(bold(1))(x.C, c, ast.small) eq.triple c : C[ast.small slash x]$],
  )
]

== *自然數類型*

#definition[
  *自然數類型*

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "NN"-FORM"$])[$Gamma vdash NN: cal(U)_i$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma "ctx"$],
    prooftrees.uni(right_label: [$" "NN"-INTRO"_1$])[$Gamma vdash 0: NN$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash n: NN$],
    prooftrees.uni(right_label: [$" "NN"-INTRO"_2$])[$Gamma vdash op("succ")(n): NN$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash n_1 eq.triple n_2 : NN$],
    prooftrees.uni(right_label: [$" "NN"-INTRO"_2"-EQ"$])[$Gamma vdash op("succ")(n_1) eq.triple op("succ")(n_2) : NN$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: NN vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c_0: C[0 slash x]$],
      prooftrees.axi[$Gamma, x: NN, y:C vdash c_s: C[op("succ")(x) slash x]$],
      prooftrees.axi[$Gamma vdash n: NN$],
    prooftrees.quart(right_label: [$" "NN"-ELIM"$])[$Gamma vdash op("ind")_NN (x.C, c_0, x.y.c_s, n): C[n slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: NN vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c_0: C[0 slash x]$],
      prooftrees.axi[$Gamma, x: NN, y:C vdash c_s: C[op("succ")(x) slash x]$],
      prooftrees.axi[$Gamma vdash n_1 eq.triple n_2 : NN$],
    prooftrees.quart(right_label: [$" "NN"-ELIM-EQ"$])[$Gamma vdash op("ind")_NN (x.C, c_0, x.y.c_s, n_1) eq.triple op("ind")_NN (x.C, c_0, x.y.c_s, n_2) : C[n_1 slash x] eq.triple C[n_2 slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: NN vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c_0: C[0 slash x]$],
      prooftrees.axi[$Gamma, x: NN, y:C vdash c_s: C[op("succ")(x) slash x]$],
    prooftrees.tri(right_label: [$" "NN"-COMP"_1$])[$Gamma vdash op("ind")_NN (x.C, c_0, x.y.c_s, 0) eq.triple c_0 : C[0 slash x]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x: NN vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma vdash c_0: C[0 slash x]$],
      prooftrees.axi[$Gamma, x: NN, y:C vdash c_s: C[op("succ")(x) slash x]$],
      prooftrees.axi[$Gamma vdash n: NN$],
    prooftrees.quart(right_label: [$" "NN"-COMP"_2$])[$Gamma vdash op("ind")_NN (x.C, c_0, x.y.c_s, op("succ")(n)) eq.triple c_s [n, op("ind")_NN (x.C, c_0, x.y.c_s, n) slash x, y] : C[op("succ")(n) slash x]$],
  )
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

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.bin(right_label: [$" "="-INTRO"$])[$Gamma vdash "refl"_a: a scripts(=)_A a$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma vdash A: cal(U)_i$],
      prooftrees.axi[$Gamma vdash a_1 eq.triple a_2 : A$],
    prooftrees.bin(right_label: [$" "="-INTRO-EQ"$])[$Gamma vdash "refl"_(a_1) eq.triple "refl"_(a_2) : a_1 scripts(=)_A a_1 eq.triple a_2 scripts(=)_A a_2$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x:A, y:A, p: x scripts(=)_A y vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, z:A vdash c: C[z, z, "refl"_z slash x, y, p]$],
      prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash b: A$],
      prooftrees.axi[$Gamma vdash q : a scripts(=)_A b$],
    prooftrees.quint(right_label: [$" "="-ELIM"$])[$Gamma vdash op("ind")_(scripts(=)_A)(x.y.p.C, z.c, a, b, q): C[a, b, q slash x, y, p]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x:A, y:A, p: x scripts(=)_A y vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, z:A vdash c: C[z, z, "refl"_z slash x, y, p]$],
      prooftrees.axi[$Gamma vdash a: A$],
      prooftrees.axi[$Gamma vdash b: A$],
      prooftrees.axi[$Gamma vdash q_1 eq.triple q_2 : a scripts(=)_A b$],
    prooftrees.quint(right_label: [$" "="-ELIM-EQ"$])[$Gamma vdash op("ind")_(scripts(=)_A)(x.y.p.C, z.c, a, b, q_1) eq.triple op("ind")_(scripts(=)_A)(x.y.p.C, z.c, a, b, q_2) : C[a, b, q_1 slash x, y, p] eq.triple C[a, b, q_2 slash x, y, p]$],
  )

  #prooftrees.tree(
    prooftrees.axi[$Gamma, x:A, y:A, p: x scripts(=)_A y vdash C: cal(U)_i$],
      prooftrees.axi[$Gamma, z:A vdash c: C[z, z, "refl"_z slash x, y, p]$],
      prooftrees.axi[$Gamma vdash a: A$],
    prooftrees.tri(right_label: [$" "="-COMP"$])[$Gamma vdash op("ind")_(scripts(=)_A)(x.y.p.C, z.c, a, a, "refl"_a) eq.triple c[a slash z] : C[a, a, "refl"_a slash x, y, p]$],
  )
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
  設 $A: cal(U)_i$，$D: (x,y: A) -> (x scripts(=)_A y) -> cal(U)_i, D(x,y,p) :eq.triple (y scripts(=)_A x)$.
  
  那麼我們就有一個項 $d :eq.triple x |-> "refl"_x : (x: A) -> D(x, x, "refl"_x)$.
  
  然後根據恆等類型的消除規則我們有，對於任何 $x,y: A, p: (x scripts(=)_A y)$，可以構造項 $op("ind")_(scripts(=)_A) (D, d, x, y, p) : (y scripts(=)_A x)$.
  
  現在對於任何 $x, y : A$ 我們可以定義期望得到的函數 $op("_")^(-1) :eq.triple p |-> op("ind")_(scripts(=)_A) (D, d, x, y, p)$.
  
  由恆等類型的計算規則，得 $("refl"_x)^(-1) eq.triple "refl"_x$.
]