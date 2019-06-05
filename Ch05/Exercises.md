# Exercises Chapter Five

## 5.2.1

\begin{align*} \texttt{or} & = \lambda \texttt{x.} \lambda \texttt{y.x tru y}
\\
\texttt{not} & = \lambda \texttt{f.}\lambda \texttt{x.} \lambda \texttt{y.f
y x}
\end{align*}

## 5.2.2

$$\texttt{scc'} = \lambda \texttt{n.}\lambda \texttt{f.}\lambda \texttt{z. (n
f) (f z)}$$

## 5.2.3

$$\texttt{times'} = \lambda \texttt{m.} \lambda \texttt{n.mn}$$

## 5.2.4

$$\texttt{pow} = \lambda \texttt{m.}\lambda \texttt{n. (n (times m))}
\texttt{c}_1$$

## 5.2.5

$$\texttt{sub} = \lambda \texttt{m.}\lambda \texttt{n.n prd m}$$

## 5.2.6

Given a term $t$, let $\tau(t)$ denote the minimal number of steps in which $t$
can be reduced to normal form (using call-by-value reductions). 

Then for any $n
\in \N$ and normal terms $f$ and $x$ we have

$$ \tau(\texttt{c}_n f x) \leq 2 + \tau(\underbrace{f \ldots f}_{\text{$n$
times}} x))$$

$$ \tau(\texttt{sub}\ \texttt{c}_m\ \texttt{c}_n) \leq 2+\tau(\texttt{c}_n\
\texttt{prd} \ \texttt{c}_m) \leq 4 + \tau(\underbrace{\texttt{prd} \ldots
\texttt{prd}}_{\text{$n$ times}} \texttt{c}_m)$$

Now

$$\tau(\texttt{prd}\ \texttt{c}_n) \leq 3 + \tau(\texttt{fst}\
(\underbrace{\texttt{ss} \ldots \texttt{ss}}_{\text{$n$ times}} \ \texttt{zz})) = O(n)$$

So

$$\tau(\texttt{sub}\ \texttt{c}_m\ \texttt{c}_n) \leq 4 + \tau(\texttt{prd}\
\texttt{c}_m) + \tau(\texttt{prd}\ \texttt{c}_{m-1}) + \ldots
+ \tau(\texttt{prd}\ \texttt{c}_{\text{max}(0, m-n)}) = O(m^2 + n)$$

## 5.2.7

$$\texttt{equal} = \lambda \texttt{m.}\lambda \texttt{n.and (iszro (m prd n)) (iszro (n prd
m))}$$

## 5.2.8

\begin{align*}
\texttt{nil} & = \lambda \texttt{f.}\lambda \texttt{c.c} \\
%
\texttt{cons} & = \lambda \texttt{x.} \lambda \texttt{xs.} \lambda
\texttt{f.}\lambda \texttt{c.f x (xs f c)} \\
%
\texttt{isnil} & = \lambda \texttt{l.l (}\lambda \texttt{x.}\lambda
\texttt{c.fls}\texttt{) tru} \\
%
\texttt{head} & = \lambda \texttt{l.l fst nil} \\
%
\texttt{tail} & = \lambda \texttt{l.fst (l (} \lambda \texttt{x.}\lambda
\texttt{c.pair (snd c) (cons x (snd c))} \texttt{) (pair nil nil))}
\end{align*}
