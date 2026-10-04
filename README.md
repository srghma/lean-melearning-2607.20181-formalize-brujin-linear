This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
## Layout

Files under `RequestProject/` are grouped by the section of the paper (`LSFA9.tex`) they formalize:

| Directory | Paper section | Contents |
| --- | --- | --- |
| `Sec2SimplyTyped/` | §2 Simply typed λ-calculus in de Bruijn notation | types, terms, `occ`/`fv`, (quasi-)linear terms (`Syntax`), environments and Fig. 2 (`Typing`), examples |
| `Sec3FragmentaryEnv/` | §3 Fragmentary typing environments | quasi-types, fragmentary environments and `+`/`−`/`⊑` (`FEnv`, `FEnvLemmas`, incl. `qtSimpleEq`/`envSimpleEq`), Fig. 3 (`Typing`), `fst2fll`/`fll2fst` (`FLL`), examples |
| `Sec4LinearTyping/` | §4 A type system for the linear λ-calculus | Fig. 4, compatible/minimal environments (`Typing`), `subeq`, quasi-linearity, `ll2st`, `st2ll`, linear-term characterization, `envarith` (`LL`), `envdefined` (`EnvDefined`), examples |
| `Sec5BetaReduction/` | §5 β-reduction with de Bruijn indices | lifting, substitution, β-contraction/reduction (`Beta`) |
| `Sec6SubjectReduction/` | §6 Subject reduction | inversion lemmas (`Inversion`), `l3`, `philippe`, `sr`, subject reduction (`SubjectReduction`) |

Material that is not part of the paper lives in `Toy/`, grouped by topic:

| Directory | Contents |
| --- | --- |
| `Toy/Types/` | toy type grammars (`Ty`, `Nominal`) |
| `Toy/Terms/` | toy typed term grammars (`Term`, `Anf`, `Open`, `NominalTerm`) |
| `Toy/LinearLogic/` | toy linear-logic sequent calculi (`Resource`, `LinearLogic`, `LinearLogic2`) |
| `Toy/Examples/` | example programs for the toy grammars (`Basic`, `Open`, `Nominal`, `LinearLogic`) |

`Main.lean` is a standalone project settings file and is not part of the formalization.
