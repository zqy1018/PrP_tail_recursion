# PrP_tail_recursion
a PrP project focused on implementing and verifying tail recursions

My work: Adapt the conversion function to weaker constraints, such as dealing with nested pattern match, function abstration and the case where the recursive function appears in the arguments of the recursive function itself.

---

Explanation of why we need an extra argument [fuel] in the conversion function of [Argument.v], which deals with the case where the recursive function appears in the arguments of the recursive function itself:

Since Coq guarantees that every function defined in Coq will terminate on all inputs, when we try to define a recursive function, we must gurantee that certain argument is decreasing. That is to say we can make recursive calls only on strictly smaller values of that argument.

We know the definition of the syntax tree of our stlc language:
```
Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  
  | tconst : nat -> tm
  | tplus : tm -> tm -> tm
  | tminus : tm -> tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm
  
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
  
  | tleaf : tm -> tm
  | tnode : tm -> tm -> tm -> tm
  | tbcase : tm -> string -> tm -> string -> string -> string -> tm -> tm
  
  | tlet : string -> tm -> tm -> tm
  
  | tfix  : tm -> tm.
```
If a function accepts an argument of type [tm], when the argument turns out to be of form [app t1 t2], according to the "decreasing principle" our next recursive call can only be on [t1] or [t2], otherwise it will not be accepted.

When the input involves the case where the recursive function appears in the arguments of the recursive function itself, such as:

<center><{f n1 (1 + f n2 n3)}></center>

The correct result of conversion is:
<center><{f n2 n3 (\ res1, f n1 (1 + res1) (\ res2, k res2))}></center>

We need to go through intermediate steps:
<center><{f n1 (1 + f n2 n3)}></center>
<center>-> <{f n2 n3 (\ res1, f n1 (1 + res1))}></center>
<center>-> <{f n2 n3 (\ res1, f n1 (1 + res1) (\ res2, k res2))}></center>

Here when we come across the intermediate result [f n1 (1 + res1)] as the argument, we need to make a recursive call on the whole body instead of anyone of its part, so the function will not be accepted if we chose the function body as the decreasing argument.