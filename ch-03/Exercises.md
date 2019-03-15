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
