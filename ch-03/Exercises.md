# Exercises Chapter Three

## 3.2.4

In general, if $s_n = \# S_n$ denotes the number of elements of $S_n$, then

$$ s_{n+1} = 3 + 3\cdot s_n + s_n^3 $$

This formula holds because each expression can be parsed *uniquely*. We get

\begin{align*}
   s_0 & = 0 \\
   s_1 & = 3 \\
   s_2 & = 3 + 9 + 27 = 39 \\
   s_3 & = 3 + 3\cdot 39 + (39)^3 = 156
\end{align*}

## 3.2.5

That the sequence $S_i$ is cumulative (i.e. *monotone*) is not completely
obvious, contrary to intuition, as the elements of $S_{i+1}$ are defined in
terms of *constructors* that take elements of $S_i$ as arguments. In
particular, if $S_i$ just was some arbitrary set and $S_{i+1}$ was defined in
according to the inductive rule, then $S_i$ certainly wouldn't be a subset of
$S_{i+1}$.

What we need really need to exploit to show this is that we know the
structure of $S_i$. In particular, we need to exploit the fact that $S_0
= \emptyset$.

\begin{lemma} If $S_i \subseteq S_{i+1}$, then $S_{i+1} \subseteq S_{i+2}$.
\end{lemma}
\begin{proof}
   Each element of $S_{i+2}$ is of the form
   $$f x_1 \ldots x_n$$
   where $f$ is some constructor and the $x_j$ are some terms lying in
   $S_{i+1}$. The same description holds for $S_{i+1}$ but with the $x_j$ lying
   in $S_i$. Since $S_i \subseteq S_{i+1}$ by assumption, it follows that
   $$ S_{i+1} \subseteq S_{i+2} $$
\end{proof}

\begin{cor} For all $i$
$$S_i \subseteq S_{i+1}$$
\end{cor}
\begin{proof} By induction over $i$. It's trivially true for $i=0$, and the
lemma above takes care of the induction step.
\end{proof}

## 3.3.4

\begin{proof}[Proof of the Principles of Induction on Terms]
   The first two principles follow quite easily from the last one (structural
   induction), hence we content ourselves with its proof. Using the description
   of the set $S$ of terms as a union
   $$ S = \bigcup_i S_i $$
   we proceed by induction over $i \in \N$. So let $P(s)$ be some predicate,
   and let the assumption of the principle of structure induction hold. We then
   show that
   $$ \text{$P(s)$ holds for all $s \in S_i$}$$
   by induction over $i$.

   For $i = 0$, there is nothing to prove. For the induction step assume that
   $P(s)$ holds for all $s \in S_i$. We need to show that $P(s)$ for all $s \in
   S_{i+1}$. But this follows immediately, since all the immediate subterms of
   a terms $s \in S_{i+1}$ lie in $S_i$ by construction.
\end{proof}

## 3.5.5

The induction principle used in the proof of Theorem 3.5.4 can be viewed as an
instance of the principle of *induction over well-founded partially ordered
sets*, with the set in question "the set of derivations" and the partial order
being the "subtree relation".

However that's not very precise, so let us make it so and get rid of those
scare quotes.

First of all, let's agree that we have fixed an alphabet $\Sigma$ containing all
letters $\texttt{a}, \ldots, \texttt{z}, \texttt{A}, \ldots, \texttt{Z}$ as well
as the symbol $\rightarrow$. On the set of strings (of finite length) there is
a concatenation operation, which we will denote by placing two strings
together, e.g. if $t_1$ and $t_2$ are metavariables denoting the strings
\texttt{my} and \texttt{lady}, then
$$t_1\texttt{fair}t_2$$
denotes the string \texttt{myfairlady}. Note that this notation is a priori
ambiguous, since an expression like \texttt{xy} can be either read as the
concatenation of the strings \texttt{x} and \texttt{y}, or as the string
\texttt{xy}; but, since both of these denote the same string, this ambiguity is
only in the sense, not the denotation.

Second, let's agree that an $n$-fold ($n \geq 1$) cartesian product of sets
$$X_1 \times \ldots \times X_n$$
is defined inductively in terms of an $n-1$-fold cartesian product and the
usual (binary) cartesian product as
$$X_1 \times \ldots \times X_n \equiv X_1\times (X_2\times \ldots X_n)$$
, where by definition the $0$-fold cartesian product is equal to
$$() \equiv \{\texttt{nil}\}$$
and the set $\texttt{nil} \equiv \emptyset$ is not a pair^[Why not?].

Note that according to this definition, *the $2$-fold cartesian product is
different from the (binary) cartesian product*, and the $1$-fold cartesian
product of a set $X$ is not equal to $X$ but to
$$X \times ().$$

This may seem like a silly definition, but this is the standard way to
introduce lists in the context of programming languages, and moreover it is the
*correct* way if you want to be able to talk about the $i$-th element of an
$n$-tuple without knowing a priori whether $n = i$ or $n > i$.

With that being said, $n$-tuples are accordingly defined via induction by the
definitional equality
$$(x_1, \ldots, x_n) \equiv (x_1, (x_2,\ldots, x_n))$$
and the convention that the $0$-tuple (not to be confused with the $0$-fold
cartesian product) is equal to
$$() \equiv \texttt{nil}$$
In particular, a $1$-fold tuple is equal to
$$(x) \equiv (x,\texttt{nil})$$

With these definition made, we have operators $\car$ and
$\cdr$ operating on sets, whose values on pairs are defined to be
$$\car((x,y)) = x,\quad \cdr((x,y)) = y$$
In particular, we get
$$\car(\cdr((x,y,z)) = y,\quad \car(\cdr(\cdr((x,y,z))))) = z$$

Let us now consider the set $\mathcal{T}$ of terms in the sublanguage of
boolean expressions, and let us define the set of potential reduction expressions
(as a sublanguage of the language defined above):

\begin{defn}
The set $\mathcal{RDE}$ of potential reduction expressions is given by
$$\mathcal{RDE} := \{ t_1\rightarrow t_2 \ :\ t_1, t_2 \in \mathcal{T}\}$$
\end{defn}

Our goal is to define the set of derivations as the set of inductive sets of
the form

$$d = (r, e, d_1, \ldots, d_1)$$

where $r \in \{ \texttt{E-IfTrue}, \texttt{E-IfFalse}, \texttt{E-If}\}$ is
a derivation rule, $e$ is a reduction expression, and $d_1$, \ldots, $d_n$
are derivations which derive reduction expressions $e_1$, \ldots, $e_n$.

\begin{defn}
   The set $\mathcal{D}$ of derivations (of reduction expressions) is the
   smallest set such that it contains
   \begin{itemize}
   \item $(\texttt{E-IfTrue}, \texttt{if true then }t_1\texttt{ else
   }t_2\rightarrow t_1)$
   \end{itemize}
   and
   \begin{itemize}
   \item $(\texttt{E-IfFalse}, \texttt{if false then }t_1\texttt{ else
   }t_2\rightarrow t_2)$
   \end{itemize}
   for all $t_1, t_2 \in \mathcal{T}$, and
   \begin{itemize}
   \item $(\texttt{E-If}, \texttt{if }t\texttt{ then }t_1\texttt{ else
   }t_2\rightarrow\texttt{if }t'\texttt{ then }t_1\texttt{ else }t_2,d)$
   \end{itemize}
   for all $t,t',t_1, t_2 \in \mathcal{T}$ and all $d \in \mathcal{D}$ for which
   $$\texttt{car}(\texttt{cdr}(d)) = t\rightarrow t'.$$
\end{defn}

\begin{rmk}
Note that it follows immediately from the definition that every element of
$\mathcal{D}$ has the form
$$(r,e,d_1,\ldots d_n)$$
where $r \in \{\texttt{E-IfTrue}, \texttt{E-IfFalse}, \texttt{E-If}\}$ and $e
\in \mathcal{RDE}$. The element $e$ is to be interpreted as the \textit{conclusion} of
the derivation and the $d_i$ as the \textit{premises} (or
\textit{subderivations}). In particular, the elements where $n = 0$ correspond
to the axioms.
\end{rmk}

We can now endow $\mathcal{D}$ with a well-founded partial order relation:

\begin{defn}
Given $d, d' \in \mathcal{D}$, we put
$$d' \prec d \quad \Leftrightarrow\quad \exists d_1,\ldots,d_n \in \mathcal{D},\ 1 \leq i \leq n\ \ d = (r,e,d_1,\ldots,d_n),\ d' = d_i$$
and when $d' \prec d$, we say $d'$ is an \textbf{immediate subderivation} of
$d$.

Moreover, we define the relation $<$ to be the transitive hull of $\prec$,
and when $d' < d$ we say that $d'$ is a \textbf{subderivation} of $d$.
\end{defn}

\begin{rmk}
Note that in the above definition of $\prec$, the number $n$ and the elements
$r,e,d_1,\ldots,d_n$ are uniquely determined by $d$ and the relation $d
= (r,e,d_1,\ldots,d_n)$.

This is not completely obvious, because a priori we
could expand an expression like $(r,e,d)$ further into $(r,e,d_1,\ldots,d_n)$
if $d$ would expand like $d = (d_1,\ldots,d_n)$. However, for $d \in
   \mathcal{D}$ we always have $\car(d) \in
   \{\texttt{E-IfTrue},\texttt{E-IfFalse},\texttt{E-If}\}$, and the latter set
   is disjoint from $\mathcal{D}$ (because ...?).
\end{rmk}

\begin{lemma}
The relations $<$ and $\prec$ are well-founded.
\end{lemma}
\begin{proof}
Note that we eventually want to show that $<$ is a partial order (i.e. antisymmetric and irreflexive), but we won't use this in this proof (in fact, we want to deduce these properties using the well-foundedness).

What we need to show that is that every \textit{non-empty} subset of $\mathcal{D}$ has a least element
in the order $<$, or equivalently, that there cannot be a strictly descending
infinite chain
$$ \ldots < d_2 < d_1 < d_0$$
This is of course equivalent to showing that there is no infinite descending
chain
$$ \ldots \prec d_2 \prec d_1 \prec d_0$$
(since $<$ was defined to be the transitive hull of $\prec$). But, to see that
such an infinite descending chain cannot exist it suffcies to remark that if
$d' \prec d$, then
$$\texttt{length}(\car(\cdr(d)) \geq \max_{i=1,\ldots,n}
\ \texttt{length}(\car(\cdr(d'_i))) + 1$$
where $d' = (r,e,d'_1,\ldots,d'_n)$ and $\texttt{length}(l)$ denotes the lenght
of a string $l$.
\end{proof}

We can now finally formulate an induction principle for $\mathcal{D}$.

\begin{thm}
Let $P$ be a predicate defined at least on elements $d \in \mathcal{D}$. If
$$d = (r,e,d_1,\ldots,d_n) \in \mathcal{D},\ \forall i\ P(d_i) \quad
\Rightarrow \quad P(d)$$
for all $d \in \mathcal{D}$, then $P(d)$ for all $d \in \mathcal{D}$.
\end{thm}
\begin{proof}
Consider the subset
$$\Omega = \{ d \in \mathcal{D}\ :\ \neg P(p) \}$$
If this was non-empty, there'd be a minimal element $d$ for the relation
$\prec$. Writing $d = (e,r,d_1,\ldots,d_n)$, it would follow that $P(d_i)$ for
all $i$ (since $d_i \prec d$). Thus it would follow that $P(d)$ by assumption,
contradicting that $\neg P(d)$.
\end{proof}

From this we can also easily derive a principle for inductive definitions

\begin{thm}
Let $Y$ be a set and for every $r \in \{\texttt{E-IfTrue},\texttt{E-IfFalse},\texttt{E-If}\}$ let
$g_r: \mathcal{RDE} \times Y^{n(r)} \rightarrow Y$ be a function, where $n(r)$ equals
the ``arity'' of $r$ (i.e. $n = 0$ unless $e = \texttt{E-If}$, where $n = n1$).

Then there exists a unique function $f: \mathcal{D} \longrightarrow Y$ such
that for $d = (r,e,d_1,\ldots,d_n) \in \mathcal{D}$ we have
$$f(d) = g_r(e,f(d_1), \ldots, f(d_n))$$
\end{thm}
\begin{proof}
Uniqueness follows quite easily by taking two function $f,f'$ and considering
the set
$$\Omega = \{ d \in \mathcal{D}\ :\ f(d) \neq f'(d)\}$$
where they disagree. Existence follows from a similar argument by considering
\textit{partially} defined functions satisfying the desired equations and by
first showing (by the same argument) that they must agree on the intersection of
their domains of definition, then showing that every $d \in D$ occurs in the
domain of definition of some such partially defined function, and then defining
$f$ to be the union of all these partially defined functions.

The only nontrivial part of this argument is showing that each $d \in
\mathcal{D}$ occurs in the domain of definition of such a function. Assuming
that's not the case would mean assuming the set
$$\Omega' = \{ d \in \mathcal{D}\ :\ \text{$d$ does not occur in the d.o.d. of
some $f$}\}$$
is non-empty. But then it would contain an element $d$ minimal with respect to
$\prec$, and writing $d = (r,e,d_1,\ldots,d_n)$, we could (by assumption) find
functions $f_1,\ldots,f_n$ having $d_1,\ldots,d_n$ in their domain of definition
(respectively), so we can find a function $f$ having all the $d_i$ in its
domain of definition, and we are then reduced to showing that
$$f' := f \cup \{(d, g(e,f(d_1),\ldots,f(d_n)))\}$$
defines a partially defined function on $\mathcal{D}$ having values in $Y$ and
satisfying the required equation. But that's easy to see (but lengthy to spell
out), and so we are done.
\end{proof}

Note that even though the argument of the above proof seems sort-of vacuous, it
really isn't since we are at least showing that the minimal elements of
$\mathcal{D}$ (i.e. the axioms) are in the domain of definition of some
partially defined function.

Using inductive construction, we can now define the depth of a derivation:

\begin{defn}
The depth $\texttt{depth}(d)$ of a derivation $d \in \mathcal{D}$ is defined
inductively by
$$\texttt{depth}(d) = 1 + \max_{i=1,\ldots,n}\ \texttt{depth}(d_i)$$
where $d = (r,e,d_1,\ldots,d_n)$.
\end{defn}

\begin{lemma}
If $d' < d$, then
$$\texttt{depth}(d') < \texttt{depth}(d)$$
\end{lemma}
\begin{proof}
It suffices to show this for $\prec$ instead of $<$, and for $\prec$ it follows
immediately from the definition.
\end{proof}

\begin{cor}
The relation $<$ is antisymmetric and irreflexive.
\end{cor}
\hfill\qedsymbol

## 3.5.10

\begin{gather*} \inferrule*[right=\texttt{Impl}]{t \rightarrow t'}{t \rightarrow^\ast t'} \\[1em]
\inferrule*[right=\texttt{Refl}]{ }{t \rightarrow^\ast t}\hskip 1.5em
\inferrule*[right=\texttt{Trans}]{t \rightarrow^\ast t' \\ t'\rightarrow^\ast t''}{t
\rightarrow^\ast t''}
\end{gather*}

## 3.5.13

1. First, let's abbreviate

   \begin{align*}\text{(\textbf{DetEval})} & \equiv \text{3.5.4} && (= \text{Deterministic evaluation}) \\
   \text{(\textbf{ValsNorm})} & \equiv \text{3.5.7} && (= \text{values are normal forms}) \\
   \text{(\textbf{NormVals})} & \equiv \text{3.5.8} && (= \text{normal forms are values}) \\
   \text{(\textbf{NormUnq})} & \equiv \text{3.5.11} && (= \text{normal forms are unique}) \\
   \text{(\textbf{NormEx})} & \equiv \text{3.5.12} && (= \text{normal forms exist})
   \end{align*}
   because who can remember what theorem x.y.z was? Then let's recall that we
   have the (trivial) implication
   $$\text{(\textbf{DetEval})} \Rightarrow \text{(\textbf{NormUnq})}.$$
   Moreover, since a term that is normal for a given set of inference rules is
   trivially so for every subset of those rules, it follows that adding new
   inference rules preserves the validity of (**NormVals**), in particular that
   rule stays valid by adding (\texttt{E-Funny1}).

   Property (**DetEval**) is of course invalidated by adding
   (\texttt{E-Funny1}), since it competes with (\texttt{E-IfTrue}). Moreover,
   (**NormUnq**) also goes down the drain because
   $$\texttt{if true then true else false} \rightarrow true$$
   by (\texttt{E-IfTrue}) but also
   $$\texttt{if true then true else false} \rightarrow false$$
   by (\texttt{E-Funny1}) and because (**ValsNorm**) does in fact stay valid.
   The latter holds of course because we could only possibly break
   (**ValsNorm**) by introducing an inference rule whose conclusion is
   something of the form $v \rightarrow t$ (i.e. with a value before the
   reduction arrow).

   As mentioned in the text, property (**NormEx**) holds for trivial reasons as
   long as we can find a map $f:\mathcal{T} \rightarrow S$ from terms into a set
   endowed with a well-founded partial order $<$ such that
   \begin{align*} t \rightarrow t' \text{ derivable} & \quad \Rightarrow\quad f(t) < f(t')
   \hfill \tag{$\ast$}
   \end{align*}
   For our very simple boolean language, we can take $S = \N$ and $f(t)
   = \texttt{length}(t)$, and property $(\ast)$ is not spoiled by introducing
   (\texttt{E-Funny1}).

2. Let's now consider the effects of introducing
   
   $$\inferrule*[right=\texttt{E-Funny2}]{t_2 \rightarrow t_2'}{\texttt{if }t_1\texttt{ then }t_2\texttt{ else }t_3\rightarrow\texttt{if }t_1\texttt{ then }t_2'\texttt{ else }t_3}$$

   instead of (\texttt{E-Funny1}).

   By the same reasoning as before, it follows that (**NormVals**),
   (**ValsNorm**) and (**NormEx**) stay true.

   Property (**DetEval**) is invalidated, since given $t \rightarrow t'$ we can
   both derive
   $$\text{if }t\texttt{ then }t\texttt{ else }t_3\rightarrow\texttt{if }t'\texttt{ then }t\texttt{ else }t_3$$
   , using (\texttt{E-If}), and
   $$\text{if }t\texttt{ then }t\texttt{ else }t_3\rightarrow\texttt{if }t\texttt{ then }t'\texttt{ else }t_3$$
   , using (\texttt{E-Funny2}).

   So it remains to ask, does (**NormUnq**) remain valid? Intuition suggests
   that it does, despite (**DetEval**) failing, because the rule
   (\texttt{E-Funny2}) only says that we can evaluate the consequences of an
   `if then else` rules before evaluating the conditional, which seems
   harmless. 

   But to *prove* this, we shall need some version of the *Church-Rosser
   property*. Namely, letting $t\hookrightarrow t'$ denote the
   one-step-derivability relation generated by the system enlarged by
   (\texttt{E-Funny2}) and correspondingly $t\hookrightarrow^\ast t'$ its
   reflexive and transitive closure, we claim that:

   \begin{lemma}
   Given $t$ and $t'$ such that $t \hookrightarrow^\ast t'$, we can always find
   $t''$ such that $t' \rightarrow^\ast t''$ and $t \rightarrow^\ast t''$:
   $$\xymatrix{ t \ar@^{(->}[r]^{\ast} \ar[rd]^{\ast} & \ar[d]^{\ast} t' \\
    & t''}$$
   \end{lemma}
   \begin{proof}
   It suffices to prove this for $\hookrightarrow$ instead of
   $\hookrightarrow^\ast$ because the general case can be reduced to this one
   by induction, i.e. if $t_1 \hookrightarrow^\ast t_2$ and $t_2 \hookrightarrow
   t_3$ then we can apply induction hypothesis to find $t_2'$ such that $t_1
   \rightarrow^\ast t_2'$ and $t_2 \rightarrow^\ast t_2'$. Moreover, the base of the
   induction gives $t_3'$ such that $t_2 \rightarrow^\ast t_3'$ and $t_3 \rightarrow^\ast
   t_3'$. We can then apply the Church-Rosser property for $\rightarrow$ (which
   is trivial because of (\textbf{DetEval})) to find $t''$ such that $t_2'
   \rightarrow^\ast t''$ and $t_3' \rightarrow^\ast t''$:
   $$\xymatrix{t_1 \ar[rd]^\ast \ar@^{(->}[r]^\ast & t_2 \ar[d]^\ast \ar[rd]^\ast \ar@^{(->}[r] & t_3 \ar[d]^\ast \\
   & t_2' \ar[rd]^\ast & t_3' \ar[d]^\ast \\
   & & t''
   }$$
   Now to prove the version of the lemma for the one-step-evaluation relation
   $\hookrightarrow$, we will use induction on the derivation of $t
   \hookrightarrow t'$. The base in this version of induction corresponds to
   proving the statement for relations $t \hookrightarrow t'$ derived from
   inferences rules without premises (i.e. axioms): those are precisely
   (\texttt{E-IfTrue}) and (\texttt{E-IfFalse}). In these cases, we also have
   $t \rightarrow t'$ and we can simply take $t'' = t'$.

   In the induction step, we take a derivation of $t \hookrightarrow t'$ and
   assume that the statement holds for the premises of the last rule of this
   derivation. Now, the last rule is either (\texttt{E-If}) or
   (\texttt{E-Funny2}), both having exactly one premise. In the first case, it
   follows immediately that also $t \rightarrow t'$ and we can again simply
   take $t'' = t'$.

   Let us now consider the case where the last rule is (\texttt{E-Funny2}).
   Then
   \footnote{I'm
   sorry for the confusing notation here: in the context of the equation below,
   $t \rightarrow t'$ simply denotes a string. This is not to be confused with
   the statement $t \rightarrow t'$, which says that $t$ and $t'$ are related
   by the one-step-evaluation relation (in the smaller ruleset), which in turn
   means that the string $t \rightarrow t'$ can be derived. In particular, the
   statement $t \hookrightarrow t'$ doesn't mean that the string $t
   \hookrightarrow t'$ can be derived ($\hookrightarrow$ isn't even in our
   alphabet), it means that the string $t \rightarrow t'$ can be derived in the
   enlarged ruleset.}
   $$t \rightarrow t' = \texttt{if }t_1\texttt{ then }t_2\texttt{ else }t_3
   \rightarrow \texttt{if }t_1\texttt{ then }t_2'\texttt{ else }t_3$$
   i.e.
   $$t = \texttt{if }t_1\texttt{ then }t_2\texttt{ else }t_3$$
   and
   $$t' = \texttt{if }t_1\texttt{ then }t_2'\texttt{ else }t_3.$$
   Here $t_2 \rightarrow t_2'$ is the conclusion of the subderivation ending
   in the promise of the last rule. By induction assumption, the lemma holds
   for that subderivation and therefore we can find $t_2''$ such that
   $t_2 \rightarrow^\ast t_2''$ and $t_2' \rightarrow^\ast t_2''$.

   But by (**NormEx**) and (**NormVals**) for the smaller ruleset, we know that
   either $t_1 \rightarrow^\ast \texttt{true}$ or $t_1 \rightarrow^\ast
   \texttt{false}$. Using repeated application of (\texttt{E-If}), it therefore
   follows that
   $$t' \rightarrow^\ast \texttt{if true then }t_2'\texttt{ else }t_3$$
   or
   $$t' \rightarrow^\ast \texttt{if false then }t_2'\texttt{ else }t_3$$
   respectively. We can then apply (\texttt{E-IfTrue}) and
   (\texttt{E-IfFalse}), respectively, to obtain that
   $$t' \rightarrow^\ast t''$$
   where
   $$t'' = t_2' \quad \text{or}\quad t'' = t_3$$
   On the other hand, we can also derive that (respectively)
   $$t \rightarrow^\ast \texttt{if true then }t_2\texttt{ else }t_3 \rightarrow t_2$$
   or
   $$t \rightarrow^\ast \texttt{if false then }t_2\texttt{ else }t_3 \rightarrow t_3$$
   , and so $t \rightarrow^\ast t''$ in both cases.
   \end{proof}

   \begin{cor}
   Property (**NormUnq**) holds in the enlarged system.
   \end{cor}
   \begin{proof}
   If $t$ is a term and $u$ is a normal form in the enlarged system such that
   $t \hookrightarrow^\ast u$, then we can apply the lemma to conclude the
   existence of $t''$ such that $u \rightarrow^\ast u$ and $t \rightarrow^\ast
   t''$. However, since $u$ is a normal form it follows that $t'' = u$. Since
   (**NormUnq**) holds in the smaller system, it therefore follows that it
   holds for the larger one also.
   \end{proof}
