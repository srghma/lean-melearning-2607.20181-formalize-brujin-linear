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