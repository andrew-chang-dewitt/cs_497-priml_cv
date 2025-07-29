# PriML Condition Variable Implementation

## Introduction

Techniques for preventing _priority inversions_ in the use of _Condition
Variables_ (CVs) have been explored before [[Muller et al. 2023][pldi]] for use
in the PriML language. This work documents the beginning of implementing these
techniques, with the source code [hosted on GitHub][gh]. To add support for
condition variables to PriML, a few different changes are needed. First, the
core operations (`wait`, `signal`, `promote`, & `newcv`) require the
appropriate syntax added to the parser. Then, keeping in line w/ PriML's core
goals, support for enforcing priority safety of CVs at compile time must be
added to the typechecker.

## Motivating examples

To guide development of CV support in PriML, the three examples written in a C-family style in _Responsive Parallelism with Synchronization_ [[2023]][pldi] were ported to PriML:

### Example 1

A simple example, showing how a CV is initialized at a given priority as
well as how the PriML compiler will raise a type error if passing a higher
priority condition variable to a lower priority thread causes a priority

(Code translated from the C-family example (Fig. 2) [[Muller et al. 2023][pldi]]).

```sml
priority high
priority low
order low < high

fun foo (cv: cv[high]) (res: int ref) =
    let val _ =
        res := !res + 1
    in
        cmd {
            signal cv (* ill-typed *)
        }
    end

main {
    cv <- newcv[high];
    res <- ref 1;
    t <- spawn[low] { foo cv res };
    sync t
}
```

### Example 2

An example of an ill-typed producer-consumer pattern program, causing a
priority inversion where the high-priority consumer may block while waiting
for a signal from the equally high-priority producer.

(Code translated from the C-family example (Fig. 3) [[Muller et al. 2023][pldi]]).

```sml
priority high
priority low
order low < high

fun prod (cv: cv[high]) (queue: int list ref) =
    let fun loop c q n =
        let val _ =
            q := n :: !q
        in
            cmd {
                signal cv;
                loop cv queue (n + 1)
            }
        end
    in
        loop cv queue 1
    end

fun cons (cv: cv[high]) (queue: ref int list) =
    let fun loop c q =
        case q of
            nil    =>
                cmd {
                    wait cv;
                    loop c q
                }
          | x::xs =>
                loop c q
    in
        loop cv queue
    end

main {
    cv <- newcv[high];
    queue <- ref nil;
    c <- spawn[high] { cons cv queue };
    p <- spawn[high] { prod cv queue }; (* ill-typed *)
    sync p
}
```

### Example 3

A well-typed example of a producer-consumer pattern program, using CV
_promotion_ to avoid a priority inversion.

(Code translated from the C-family example (Fig. 4) [[Muller et al. 2023][pldi]]).

```sml
priority high
priority low
order low < high

fun prod (cv: cv[low]) (queue: int list ref) =
    let fun loop c q n =
        let val _ =
            q := n :: !q
        in
            cmd {
                signal cv;
                loop cv queue (n + 1)
            }
        end
    in
        loop cv queue 1
    end
fun cons (cv: cv[high]) (queue: ref int list) =
    let fun loop c q =
        case q of
            nil    =>
                cmd {
                    wait cv;
                    loop c q
                }
          | x::xs =>
                loop c q
    in
        loop cv queue
    end

main {
    cv <- newcv[low];
    queue <- ref nil;
    p <- spawn[high] { prod cv queue };
    cv2 <- promote[high] cv;
    (* would now be ill-typed to spawn prod *)
    c <- spawn[high] { cons cv2 queue };
    sync c
}
```

## Related works

In planning to implement CVs & typechecker enforement of priority safety, we
were inspired by Rust's borrow checker & associated _lifetime analysis_. In
examples 2 & 3 (above), the type system outlined by Muller et al.
[[2023][pldi]] aims to prevent priority inversion via a set of typing
restrictions based on _ownership_ of CVs & relative priority of the thread the
CV operation is being done in:

> 1. To wait on a CV with priority 𝜌, a thread's priority must be less
> 2. To wait on a CV with priority 𝜌, a thread's priority must be less than or
>    equal to 𝜌, and
> 3. To signal a CV with priority 𝜌, a thread must own or share the CV at the
>    thread's priority.
> 4. To pass any ownership of a CV at any priority to another thread, a thread
>    must own or share the CV at its own priority.
> 5. No thread may own or share a CV at a priority lower than that CV's
>    priority

To enable enforcement of these typing restrictions, PriML needs to
know what thread owns any given CV, as well as when that CV is shared & what
threads it is shared with&mdash;two concepts also seen in Rust's borrow
checker.

Our research indicated that Rust's borrow checker's tracking of ownership &
lifetimes is done as a dataflow analysis done on the control flow graph
(CFG) during compile time. In this analysis, lifetimes (the region of a CFG
that a borrow lasts for) are computed first from liveness analysis of
references, then the set of in-scope _loans_ "or a statement at point P" in the
CFG are computed using gen & kill sets based on these rules given in the NLL
RFC [[Matsakis et al. 2017][nllrfc]]:

> - any loans whose region does not include P are killed;
> - if this is a borrow statement, the corresponding loan is generated;
> - if this is an assignment `lv = <rvalue>`, then any loan for some path P of
>   which `lv` is a prefix is killed.

While PriML is a garbage collected language, meaning a borrow checker & the
related concept of lifetimes doesn't matter for most variable types, tracking
the lifetime & loans of a condition variable allows for for using dataflow
analysis to detect priority inversions.

## Overview of the Condition Variables implementation

Implementing condition variables in PriML is being done in three parts:
parsing, typechecking, & dataflow analysis. An initial sketch of the
implementation design is as follows:

1. perform liveness analysis using the external language AST on _all_ values
   (since we haven't done typechecking & don't yet know which ones are CVs)
2. use liveness analysis to compute lifetime constraints on CVs during
   typechecking & generate type constraints
3. perform dataflow analysis to compute loans on condition variables &
   detect priority inversions.

### Parser

The following language constructucts were added to the external language by
adding the necessary tokens to `./priml/el.sml` & corresponding cases to
`./priml/parser/parse.sml`:

- `v <- newcv[p]` creates a new CV at priority `p`
- `signal v` signals a CV variable named `v`
- `wait v` causes the thread to stop processing until a signal is given to the
  CV `v`
- `v' <- promote[p'] v` creates a higher priority (`p'`) handle to the same
  condition variable underlying v & stores it at `v'`

Additionally, support for specifying that an argument is a CV in a function
signature (e.g. `fun foo (v: cv) = ...`) was added (although support for
indicating what priority that CV type should have is not yet implemented).

### Dataflow

With parsing support added, the next task is to create a generic dataflow
analysis framework, which will be used to perform liveness analysis as well as
computing loans of CVs. While this part of the work is still underway, it is
composed of two main functors `Dfg` (at `./priml/df/dfg.sml`) exposing an API
for building a CFG from a given list of instructions & `Dataflow`(at
`./priml/df/dataflow.sml`) exposing the main `compute` function for computing
a dataflow analysis on a given CFG & gen/kill sets.

Next steps on the dataflow portion of the task include the following:

1. Complete the generic dataflow framework
   - Create/use a working Graph module to build the CFG from the list of
     instructions
   - Implement mutually recursive functions to translate EL constructs (e.g.
     `exp`, `cmd`, `dec`, or `prog` in `./priml/el.sml`) into CFG basic blocks
2. Implement liveness analysis using (1)
3. Implement dataflow analysis to compute in-scope loans at each CFG point
   using (1) & (2)

#### 4. Liveness analysis

Once (1) is completed, performing liveness analysis on all variables can be
done using the following steps:

1. Generate a CFG for performing analysis on using `Dfg.cfg_of_insts`
2. Compute liveness from the CFG created in (1) as a backward may analysis
   using `Dataflow.compute` with in & out equations for gen & kill sets as:

<pre><code>out[n] := ∪<sub>n'∈succ[n]</sub> in[n']
in[n]  := gen[n] ∪ (out[n] / kill[n])
</pre></code>

Considering our well-typed producer consumer example from before (Example 3),
liveness of cv & cv2 is calculated using the following CFG with in & out sets
computed from the bottom up:

```
A [ cv <- newcv[low];        ]
               |                // in[A] = out[B] = { cv }
               v
B [ p <- spawn[high] {       ]
               |                // in[B] = out[C] { cv }
               v
C [ prod cv ...              ]
               |                // in[C] = out[D] { cv }
               v
D [ cv2 <- promote[high] cv; ]
               |                // in[D] = out[E] = { cv2, cv }
               v
E [ c <- spawn[high] {       ]
               |                // in[E] = out[F] = { c, cv2 }
               v
F [ cons cv2 ...             ]
               |                // in[F] = out[G] = { c }
               v
G [ sync c                   ]
                                // initial facts: in[G] = { }
```

#### 3. Computing in-scope loans

Using the same example 3 CFG used in liveness, we can visualize the in-scope
loan dataflow analysis as a forward (top-down in the below CFG) may analysis:

```
                                // initial facts: in[A] = { }
A [ cv <- newcv[low];        ]
               |                // in[B] = out[A] = { }
               v
B [ p <- spawn[high] {       ]
               |                // in[C] = out[B] { }
               v
C [ prod cv ...              ]  // cv is loaned here...
               |                // in[D] = out[C] { cv }
               v
D [ cv2 <- promote[high] cv; ]  // cv is loaned again here...
               |                // in[E] = out[D] = { cv }
               v
E [ c <- spawn[high] {       ]  // cv no longer loaned here...
               |                // in[F] = out[E] = { }
               v
F [ cons cv2 ...             ]  // cv2 is loaned here...
               |                // in[G] = out[F] = { cv2 }
               v
G [ sync c                   ]  // cv2 no longer loaned here...
                                // out[G] = { }
```

This CFG plus the descriptions of gen & kill sets given in the NLL RFC [[Matsakis et
al. 2017][nllrfc]] (see Related Works, above) should give a good start in
deriving in/out equations for computing in-scope loans of CVs.

### Elab (typechecking)

The last remaining part to implement is typchecking. The goal of the type
checking modifications required to implement CVs is to

1. identify which values are CVs, then
2. generate constraints for CVs on lifetimes using liveness analysis, and
3. generate related subtyping constraints on lifetimes, before finally
4. solving those constraints to find the actual lifetimes of the CVs identified
   in (1)

Finally, using the lifetimes found during elaboration & the in-scope loans at
each block of the CFG, the implementation needs to traverse the AST of the
program, inspecting the lifetimes & loans of each node & reporting any errors.

:::{#references}

## Refererences

Stefan K. Muller, Kyle Singer, Devyn Terra Keeney, Andrew Neth, Kunal Agrawal,
I-Ting Angelina Lee, and Umut A. Acar. 2023. Responsive Parallelism with
Synchronization. _Proc. ACM Program. Lang. 7_, PLDI, Article 135 (June 2023),
24 pages. [https://doi.org/10.1145/3591249](https://doi.org/10.1145/3591249)

[pldi]: https://doi.org/10.1145/3591249 "Responsive Parallelism with Synchronization"

Niko Matsakis. 2018. An alias-based formulation of the borrow checker. (April
2018). Retrieved May 22, 2025 from
[https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/](https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/)

[nllblog]: https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/ "An alias-based formulation of the borrow checker"

Niko Matsakis. 2017. 2094-nll. (August 2017). Retrieved May 22, 2025 from
[https://rust-lang.github.io/rfcs/2094-nll.html](https://rust-lang.github.io/rfcs/2094-nll.html)

[nllrfc]: https://rust-lang.github.io/rfcs/2094-nll.html "Rust RFC 2094: NLL"
[gh]: https://github.com/smuller/PriML-lang/tree/condvar "PriML language implementation, condition variable feature branch"

:::
