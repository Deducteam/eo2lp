
We need to implement a mechanism for binding free schematic
variables in post-elaboration commands. e.g.;
```
Elaborating: (define @pair () @@pair)

  Begin resolving `@@pair⟨U ↦ ?U0, T ↦ ?T0⟩`
  Resolved:
    `@@pair⟨U ↦ ?U0, T ↦ ?T0⟩`
  with type
    `(~> ?U0 ?T0 ((@Pair⟨⟩ ⋅ ?U0) ⋅ ?T0))`

Done:
  define @pair⟨⟩
    : (~> ?U0 ?T0 ((@Pair⟨⟩ ⋅ ?U0) ⋅ ?T0))
    := @@pair⟨U ↦ ?U0, T ↦ ?T0⟩
```

We need to update the signature so that @pair has two
parameters {U, T} and then update the body of the
definition with this assignment.

Some procedure called 'bind_svars'.
For each free schematic var, we choose a name.

  SVar (s,0) -> Var s
  SVar (s,i) -> Var (s ^ string_of_int i)

We use this list of variables as our (implicit) parameters for @@pair.
Then we replace the schematic vars in the body with our choice
using `svmap_subst`.


# 2025-12-20

(* (unresolved) metavars can only come from constants.
  so really, a 'parameter map' should hold the parameters,
  along with some information about its instantiation.
  kind of like an option type.

  so to collect all free mvars, we need to look at all
  constants and their parameter maps. if it maps to a
  metavariable, we consider it 'free'

*)

can we simplify mvmaps and param maps??
it feels like we shouldn't need both.

consider changing Const constructor to just take a string
and a list of terms for the parameter instantiations.
when we initialize, we lookup the params of the constant
in the signature, then generate metavars for them.

for binding lingering mvars, we need to be able to know
the type of the metavar. otherwise, there's no need to
remember the 'original initialization site' of the metavar.

it just matters that they have unique names.
do this after lunch and chores.


also, it's quite important that we consider how params
are handled during desugaring and resolution.

# 2025-12-21

It feels possible that elaboration should process the
local context (param list), followed by the body.
  Perhaps there are constraints generated in the local
context that cannot be resolved alone (without the
constraints generated when inferring the body).
  But I'm skeptical of this. I think we just need to
elaborate the parameters sequentially.
