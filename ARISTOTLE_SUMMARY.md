# Summary of changes for run a45a2c14-2409-49a9-aeba-3c4920e8da87
I grouped the project's files into directories: paper material by the section of `LSFA9.tex` it formalizes, and the toy material (not part of the paper) by topic. The whole project rebuilds with no errors, no warnings and no `sorry`. No theorem statements or proofs changed. The only code edits are moving declarations between files and updating `import` lines and file headers.

**Paper sections (`RequestProject/`)**
- `Sec2SimplyTyped/` (§2)
  - `Syntax.lean`: types, terms, `occ`, `fv`, subterms, quasi-linear and linear terms.
  - `Typing.lean`: environments `Env` and the Fig. 2 system `STTyped`.
  - `Examples.lean`: the (tjdb1)/(tjdb2) examples.
- `Sec3FragmentaryEnv/` (§3)
  - `FEnv.lean`: quasi-types and fragmentary environments.
  - `FEnvLemmas.lean`: Lemmas `qtSimpleEq` and `envSimpleEq`, plus basic facts about `⊑`.
  - `Typing.lean`: the Fig. 3 system `FLLTyped`.
  - `FLL.lean`: the occurrence lemma, `fst2fll` and `fll2fst`.
  - `Examples.lean`: the (exappf) example.
- `Sec4LinearTyping/` (§4)
  - `Typing.lean`: the Fig. 4 system `LLTyped`, plus `Compatible` and `Minimal`.
  - `LL.lean`: `subeq`, quasi-linearity, `ll2st`, `st2ll`, the characterization of linear terms, and `envarith`.
  - `EnvDefined.lean`: Lemma `envdefined`.
  - `Examples.lean`: the (ex2dbn) example.
- `Sec5BetaReduction/Beta.lean` (§5): lifting, substitution, β-contraction and β-reduction.
- `Sec6SubjectReduction/` (§6)
  - `Inversion.lean`: inversion lemmas.
  - `SubjectReduction.lean`: `l3`, `philippe`, `sr`, and subject reduction (single and multi-step).

Three old files each mixed several sections, so I split them along section lines:
- `Syntax.lean`: §2 and §5.
- `Typing.lean`: Figures 2, 3 and 4.
- `Examples.lean`: examples from §2, §3 and §4.

I also moved some lemmas so that no section depends on a later one. The `⊑`/environment facts and the quasi-linear subterm facts that §3 needs used to sit in the §4 file. They now live in §3 and §2.

**Toy material, by topic (`RequestProject/Toy/`)**
- `Types/`: `Ty`, `Nominal`.
- `Terms/`: `Term`, `Anf`, `Open`, `NominalTerm`.
- `LinearLogic/`: `Resource`, `LinearLogic`, `LinearLogic2`.
- `Examples/`: `Basic` (formerly `Examples`), `Open`, `Nominal`, `LinearLogic`. These were formerly `OpenExamples`, `NominalExamples` and `LinearLogicExamples`.

File references inside the docstrings now use the new paths. `Main.lean`, a standalone settings file, stays at the top level. I added a "Layout" section to `README.md` with this table.

I updated the file locations in the Properties table for each entry I could match to a moved file. I could not read the full table, so a few toy entries may still point to their old paths; their descriptions may also mention old paths. Every theorem is still proved under its old name.

# Summary of changes for run f259818d-b495-4f41-866b-f6cecb599dde
I added ToyLinearLogic and ToyLinearLogic2 in four new files under `RequestProject/Toy/`. The whole project builds with no `sorry` and no warnings. The main theorems use only Lean's standard axioms. The earlier files are unchanged.

**How I read "using ANFtyped".** I took it to mean the style of your typed A-normal grammar (`Toy/Anf.lean`): a derivation is a typed proof term, an inductive family indexed by what it proves, with one constructor per rule. I also connected the two: `Anf.lean` statements translate into proofs in both new calculi. If you meant something else, let me know.

**`LinearLogic.lean`: ToyLinearLogic**
- `Fml` has atoms, `A^⊥`, `⊗`, `⅋`, `&`, `⊕`, `!` and `?`. `CLL Γ Ψ` is the type of derivations of `Γ ⊢ Ψ`, with one constructor for each rule on your page: initial sequent, cut, both exchanges, and the left and right rules for `⊥`, `⊗`, `⅋`, `&`, `⊕`, `!` and `?`, including `! R` and `? L`. Sequences are lists read left to right, so `Γ, A` is `Γ ++ [A]`.
- `Derivable.perm`: exchange works for any reordering of either side.
- `A ⊸ B` is defined as `A^⊥ ⅋ B`, and its right and left rules are derived (`lolliR`, `lolliL`). There are small example derivations: `A⊗B ⊢ B⊗A`, `A ⊢ A^⊥^⊥`, `⊢ A ⅋ A^⊥`, `!A ⊢ !A⊗!A` and `!A ⊢ !!A`.
- **Typed A-normal terms are proofs** (`Stmt.toCLL`, `AProgram.toCLL`). A statement `{Γ} s : α {Δ}` gives a derivation of `!Θ, used ⊢ ⟦α⟧`, where `used` lists the variables it consumed and `α → β` is read as `⟦α⟧ ⊸ ⟦β⟧`.
  - **Why the extra `!Θ`:** constants can be used many times, and a base-type literal such as `1 : nat` cannot be proved from nothing. So the constants enter as reusable `!`-hypotheses.
  - `AProgram.toCLL_of_list` takes `Θ` to be the constants' own types. `AProgram.toCLL_of_isEmpty` gives `⊢ ⟦α⟧` when there are no constants.

**`LinearLogic2.lean`: ToyLinearLogic2 (Hodas–Miller style)**
- `IO Γ Δ` is the type of derivations `{Γ} t {Δ}`. The environments are lists of slots holding signed formulas: `L A` is a hypothesis, `R A` a conclusion, and an empty slot is a formula already used, like the paper's `⊥`.
- `Proves Γ A Δ` is the judgement `{Γ} t : A {Δ}`.
- **How the rules work:**
  - Each rule picks its main formula by position, like the paper's variable rules. It adds the new formulas as slots that must be empty by the end of the premise, like rule (abs).
  - Cut, `R⊗` and `L⅋` pass the environment from the first premise to the second, like rule (app). `R&` and `L⊕` run both premises between the same environments.
  - `! R` and `? L` require everything else they use to be a `!`-hypothesis or a `?`-conclusion.
  - There is no exchange rule, since picking by position already allows any order.
- **Proved results:**
  - Soundness (`IO.sound`): an `IO` derivation gives a ToyLinearLogic derivation of the formulas it used.
  - Completeness (`CLL.toIO`): a ToyLinearLogic derivation gives an `IO` derivation between any two environments whose used formulas are that sequent, in any order.
  - Hence both calculi prove the same sequents (`derivable_iff_io`).
  - `Stmt.toIO`: a statement `{Γ} s : α {Δ}` gives `{Γ, !Θ} t : ⟦α⟧ {Δ, ⊥…⊥}`, with the same environments.
- A concrete example, `tensorCommIO`, proves `A⊗B ⊢ B⊗A` with no exchange step.

**Supporting and example files**
- `Resource.lean` has the environment bookkeeping both calculi share. Its key facts are that what gets used adds up along a chain of environments, and that any split of it can be matched by an intermediate environment.
- `LinearLogicExamples.lean` reads `lenSuccA` from `Toy/Examples.lean` as a proof of `string ⊸ nat` in both calculi, with the six constant types as `!Θ`.

The Properties table has two new definitions (`CLL`, `IO`) and three new proved properties: the A-normal translation into ToyLinearLogic, the equivalence of the two calculi, and the translation into ToyLinearLogic2.

# Summary of changes for run a78c41a7-2bd8-4286-b5e4-9e4cbf2055ff
I added a fourth toy grammar. The earlier toys (`Toy/Ty.lean`, `Term.lean`, `Anf.lean`, `Open.lean` and their example files) mostly copied your *term* file. This one copies two ideas from your *type* file that none of them had: datatypes that are declared once and referred to by a de Bruijn name, and a delay that cannot be nested. It is in three short files under `RequestProject/Toy/`. They build with no `sorry` and no warnings. The main theorems use only Lean's standard axioms (`propext`, `Quot.sound`, plus `Classical.choice` for the linearity result).

**`Nominal.lean`: types**
```
NTy n d ::= base b | fn NTy NTy
          | data r             -- r : Fin n, a declared datatype by de Bruijn name
          | lazy (NTy n false) -- a delay, only at index d = true
```
- **Delays:** as in your file, the second index is optional (`NTy n` means `NTy n true`), and a delay holds an `NTy n false`, so a delay inside a delay cannot be written (`lazy_not_in_lazy`). There are `relax`, `undelay` and `isDelay`, and `mkLazy` reads `Unit → Unit → τ` as a single delay (`mkLazy_mkLazy`, `mkLazy_relax`).
- **Renaming:** `map`, `map_id` and `map_map`, as in your file. `weaken` renames with `Fin.succ` when a new datatype is declared.
- **Link to the paper:** `toTy` translates a toy type to one of the paper's simple types, with the leaves and datatype names as atoms. It forgets the delay, since a delay stands for the value it holds (`toTy_mkLazy`, `toTy_relax`, `toTy_map`).

**`NominalTerm.lean`: terms**
```
NNeu ::= var | const c | app NNeu NNf | force NNeu
NNf  ::= neu NNeu | lam NNf | delay NNf
```
Each term is indexed by the paper's judgement `{Γ} t : α {Δ}`: the variables available before, the type, and the variables left over. The constructors of a datatype are constants. `force` only accepts a neutral term, so a forced literal delay `force (delay t)` cannot be written; this is the toy version of your rule that a force needs an open delay. Proved results:
- `NNf.sound`: once delays are removed from the term, every normal form is accepted by the paper's typing system (Figure 4).
- `NNf.quasiLinear`: each variable is used at most once, and each λ uses its parameter exactly once.
- `NNf.normal`: a normal form contains no β-redex.
- `NProgram.linear`: every closed program is a linear λ-term, simply typed with no free variables.

**`NominalExamples.lean`**
One declared datatype, `data 0`, stands for lists of naturals. Two programs, each with an `rfl` check of what it translates to:
- `consLazy`: `λx. λxs. delay (cons x xs)`.
- `forceCons`: `λt. cons zero (force t)`.

It also checks that both programs are linear, that `mkLazy (mkLazy natList)` is a single delay, and that weakening renames `data 0` to `data 1`.

**Simplifications:** datatypes are opaque names whose constructors are constants. There is no signature giving their unfoldings, and no records, unions, enums or thunks. There is one kind of delay, not two. I added the new type grammar and its two groups of results to the Properties table.

# Summary of changes for run 417bfb5a-bb89-4df1-a552-ea5a82c6b711
I added a third toy grammar, `RequestProject/Toy/Open.lean`, with examples in `RequestProject/Toy/OpenExamples.lean`. It copies the central idea of your normal-form `Term` file: split *known* from *unknown* values, track whether each expression is open or closed, and require every elimination to have an open operand. Both files build with no `sorry`. The main theorems use only Lean's standard axioms (`propext`, `Quot.sound`, and `Classical.choice` for the linearity result).

The earlier toy files (`Toy/Ty.lean`, `Term.lean`, `Anf.lean`, `Examples.lean`) are unchanged.

**The grammar.** Like the earlier toys, each class is indexed by the paper's judgement `{Γ} t : α {Δ}` (the variables available before and after), plus an open/closed flag `o : Bool`:
```
Neu   Γ α Δ    ::= var x | app Neu (PExpr o)
                 | extern c (Args o) (o = open)   -- full call of a constant, ≥1 open argument
PExpr Γ α Δ o  ::= neu Neu        -- open
                 | lit c          -- closed (a constant of base type)
                 | lamC PExpr     -- closed: the body uses only its own parameter
                 | lamO PExpr (Γ ≠ Δ)   -- open: comes with a proof that it uses an outer unknown
Args  Γ σs Δ o ::= nil | cons PExpr Args   -- open iff some argument is
```
`lamC`/`lamO` play the role of your `Body.closed`/`Body.opened`, and `extern`'s condition matches your `extern e args (h : o = some ℓ)`.

**Proved results:**
- **The open/closed flag is exact** (`PExpr.closed_iff`): an expression is closed exactly when it uses no unknown, i.e. `Γ = Δ`. The proof uses the paper's Lemma `subeq` and a new antisymmetry lemma for `⊑` (`FEnv.le_antisymm`).
- **Every neutral term uses an unknown** (`Neu.uses_unknown`). So every application uses an unknown (`PExpr.app_uses_unknown`), and a closed expression is a literal or a λ (`PExpr.closed_isValue`).
- **A closed program is closed** (`OProgram.closed`): it is a literal or a λ, never a computation. This is the toy version of your `closed_isValue`.
- **Results carried over from the first toy grammar:** each expression is typed by the paper's system with the same environments (`PExpr.sound`). It uses each variable at most once and each λ-parameter exactly once (`PExpr.quasiLinear`), and contains no β-redex (`PExpr.normal`). Every closed program is a linear λ-term, simply typed with no free variables (`OProgram.linear`).

**Examples** (`OpenExamples.lean`):
- `succO`: `λx. add x 1`, a closed λ whose call is stuck on the unknown `x`.
- `applyO`: `λf. λx. f x`. The inner λ is open because it uses `f`; the outer λ is closed.
- `no_add_one_two`: `add 1 2`, a redex between known values, cannot be written as a program.

The two examples have `rfl` checks of what they translate to in the paper's terms.

**Simplifications:** the open/closed flag is a `Bool`, not a nesting level (`Option Nat`). Constants of function type can only be fully applied, never passed around as values. There are no `let`s, join points, records, unions or delays.

The Properties table now lists the new grammar and its two main results.

# Summary of changes for run dcabc14b-0e68-4f6a-a46d-8dbd0fc4d522
The project already had a toy grammar in the style of your two files, from the previous session, in `RequestProject/Toy/`: `Ty.lean` (types), `Term.lean` (terms) and `Examples.lean`. I rebuilt it and it still compiles with no `sorry`. I also added a second term grammar, `RequestProject/Toy/Anf.lean`, which follows the layered structure of your `Val`/`Comp`/`Term` file more closely. It builds with no `sorry`, and its main theorems use only Lean's standard axioms.

**What was already there**
- **Types:** the paper's simple types, read as linear arrows `σ ⊸ τ`, over three leaf types `nat | bool | string`.
- **Terms:** `Var`, `Tm`, and a β-normal part `Neu`/`Nf`. Each is indexed by the paper's judgement `{Γ} t : α {Δ}`: an input environment, a type, and an output environment listing the variables not yet used.
- **Proved results:**
  - The typed terms are exactly the terms the paper's typing system accepts.
  - Normal forms contain no β-redex, and every β-normal typed term can be written as one.
  - Every closed program is a linear λ-term.
  - Typed terms stay typed under β-reduction.

**What's new in `Toy/Anf.lean`**
```
Head Γ α Δ ::= var Var | const c     -- what can be called: never a λ
Val  Γ α Δ ::= head Head | lam Stmt  -- a function's parameter must be used
Comp Γ α Δ ::= app Head Val          -- one call
Stmt Γ α Δ ::= ret Val | letE Comp Stmt   -- let x := c; body, with x used exactly once
```
- **What cannot be written:** a variable used twice; a parameter or `let`-bound variable that is never used; a call whose function is a `λ`.
- **Proved results:**
  - Every layer is accepted by the paper's typing system with the same environments (`Head.sound`, `Val.sound`, `Comp.sound`, `Stmt.sound`).
  - Every statement uses each free variable at most once, and each `λ` and `let` uses its variable exactly once (`Stmt.quasiLinear`).
  - Every closed program is a linear λ-term, simply typed with no free variables (`AProgram.linear`).
  - The function in a call is never a `λ` (`Comp.head_ne_lam`).
  - The result of β-reducing a statement can still be written in the first toy grammar, with the same environments (`Stmt.subject_reduction`).

**One design choice to be aware of:** `let x := c; body` translates to `(λ body) c`. Because the paper's application rule passes the environment through the function before the argument, `body` is typed first and `c` uses only the variables that `body` leaves over. This is why `Stmt.letE` lists its environments in that order.

**New examples in `Toy/Examples.lean`**
- `lenSuccA`: `λs. let n := length s; let f := add n; let r := f 1; r`. A `rfl` check confirms what it translates to.
- `no_anf_add_self_self`: proves that `λx. let y := add x; y x` cannot be written, because it uses `x` twice.

**What the toy leaves out:** your files' level tracking (open vs. closed), the separate contexts for known and unknown values, usage counts other than exactly once, delays, records, unions and join points. The Properties table now includes the new grammar and its linearity theorem.

# Summary of changes for run 147a9b3c-a46f-4c46-bf4e-9414e0f54d15
I built a small toy grammar in the style of your two files, on top of the existing formalization of the paper. It builds with no `sorry`, and the main theorems use only Lean's standard axioms. The new files are under `RequestProject/Toy/`.

**`Ty.lean` — types.** The types are the paper's simple types, read as linear arrows `σ ⊸ τ`, with three leaf types (`Base ::= nat | bool | string`). There are abbreviations `LTy.nat`, `LTy.bool`, `LTy.string` and `LTy.fn`, and `LTy.den` gives the Lean type each type stands for. Two small results, stated for any set of leaves:
- **Spines:** every type is `σ₁ ⊸ … ⊸ σₙ ⊸ b` in exactly one way (`Ty.args`, `Ty.result`, `Ty.ofSpine_args_result`).
- **Renaming leaves:** `Ty.map`, with `map_id` and `map_map`, as in your `Ty.map`.

**`Term.lean` — terms.** Following your `Neu`/`PExpr`, it has a docstring with the grammar table, a "what cannot be written" list, and classes indexed by their contexts. The index is the paper's Figure 4 judgement `{Γ} t : α {Δ}`: an input environment, a type, and an output environment listing the variables not yet used.
```
Var ::= here | there₁ β Var | there₂ Var          -- use one slot
Tm  ::= var | const c | app Tm Tm | lam Tm
Neu ::= var | const c | app Neu Nf
Nf  ::= neu Neu | lam Nf
Program α := Nf τ [] α []
```
`app` passes the environment from its function to its argument, so a variable can't be used twice. `lam` requires its parameter slot to be empty (`⊥`) at the end of the body, so the parameter must be used exactly once. Translating back to the paper's untyped terms (`erase`), the proved results are:
- **Matches the paper's typing exactly:** `llTyped_iff_exists_tm` says `LLTyped τ Γ t α Δ ↔ ∃ e : Tm τ Γ α Δ, e.erase = t`, built from `Tm.sound` and `Tm.complete`.
- **Normal forms:** `Nf.normal` shows a normal form contains no β-redex. `Nf.complete` shows every β-normal term that the paper's system types can be written as an `Nf`.
- **Linearity:** `Tm.quasiLinear` shows no free variable occurs twice and every `λ` binds exactly one occurrence. `Program.linear` shows every closed program is a linear λ-term, simply typed in the empty environment. `Nf.linear_of_consumes` is the version for a program that uses up a whole environment.
- **Closed under β-reduction:** `Tm.subject_reduction`, obtained from the paper's subject reduction theorem.

**`Examples.lean` — examples.** A toy set of constants (literals, `add`, `not`, `length`) with types and values, and some programs: `idNat`, `succ` (`λx. add x 1`), `lenSucc`, and `compose`, which is the paper's example `λλλ(1 (2 0))`. Two theorems show what cannot be written: `λx. add x x` (`no_add_self_self`, uses `x` twice) and `λx. 1` (`no_const_fun`, never uses `x`).

To keep it simple, the toy leaves out your file's level tracking (open vs. closed), its separate contexts for known and unknown values, delays, records, unions and join points. Its only constraints are linearity and β-normality.

# Summary of changes for run 514d6c35-c8f9-41a6-bd2f-457150054056
I formalized the paper in `LSFA9.tex`, "A Typing System for the Linear Lambda-Calculus in de Bruijn Notation", in Lean 4 with Mathlib. Every lemma and proposition in it is proved. The project builds with no `sorry` and no added axioms: the main theorems use only Lean's standard axioms.

**Files (all under `RequestProject/`)**
- `Syntax.lean`: simple types, de Bruijn terms, `occ`, `fv`, subterms, quasi-linear and linear terms, lifting, substitution, β-contraction and β-reduction.
- `FEnv.lean` / `FEnvLemmas.lean`: quasi-types (`⊥` is `none`), fragmentary environments, and the partial `+`/`−` (an undefined result is `none`) and `⊑` operations.
  - A proof that these operations match the paper's componentwise definitions.
  - Lemmas `qtSimpleEq` (a–c), `envSimpleEq` (a–c) and `envdefined` (a–b).
- `Typing.lean`: the three typing systems — simply typed (Fig. 2), fragmentary (Fig. 3), and the main `{Γ} t : α {Δ}` system (Fig. 4) — plus *compatible* and *minimal* environments.
- `FLL.lean`: the occurrence lemma for Fig. 3, and Propositions `fst2fll` and `fll2fst`.
- `LL.lean`: Lemma `subeq`, Lemma `quasi-linearity-aux`, Propositions `quasi-linearity`, `ll2st` and `st2ll`, the characterization of linear terms, and Lemma `envarith` (a–b).
- `Inversion.lean`: supporting lemmas (inversion rules and environment splitting).
- `SubjectReduction.lean`: Lemmas `l3`, `philippe` (lifting) and `sr` (substitution), the subject reduction theorem, and its extension to multi-step β-reduction.
- `Examples.lean`: examples from the paper — `λ(1 0)` is linear, `λ(2 0)` is not, the typing of `λλλ(1 (2 0))` in Fig. 4, and the fragmentary rule (exappf).

**How to read the Lean statements:** an environment is a list whose head is position 0 (the paper's rightmost entry). So the paper's `Γ, α` is `α :: Γ`, and `Γ₁, ω, Γ₂` is `Γ₂ ++ ω :: Γ₁`.

**Problem found in the paper:** the definition of an environment being *minimal* requires `(|Γ|−1) ∈ fv(t)`. That can never hold for the empty environment. Read literally, the proposition characterizing linear terms is then false for closed terms such as `λ0`: `{} λ0 : α→α {}` is derivable, but `[]` would not count as minimal. I changed the definition to require that condition only when `Γ` is nonempty; with this change the equivalence is proved in both directions.

**Differences from the paper's statements:**
- Lemma `quasi-linearity-aux` is proved for every index `i`, not just `i < |Γ|`, since the bound isn't needed.
- For the partial operations, "if all operations are defined" is written as the hypothesis that every intermediate result is `some _`.

The Properties table lists each result with its location in `LSFA9.tex`; all theorems there are marked proved.