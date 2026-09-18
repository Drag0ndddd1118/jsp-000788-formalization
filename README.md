# Formalization of JSP-000788 (Erdős Problem #948)

## Problem Overview

**Catalog ID:** [JSP-000788](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000788)  
**Erdős Problem:** [#948](https://www.erdosproblems.com/948)  
**Mathematical Area:** Number theory / Ramsey theory  

### Problem Statement
Under a finite coloring of the positive integers, can the specified sparse sequence be found whose subset sums omit at least one color?

Erdős and Galvin asked whether for every growth rate $f : \mathbb{N} \to \mathbb{N}$ and every finite coloring of $\mathbb{N}$ (or $\mathbb{Z}$), there exists a sequence $a_n$ with $a_n < f(n)$ infinitely often such that the set of finite sums $\mathrm{FS}(a)$ omits at least one color.

### Resolution
Disproved (negative answer) by Lisa Price and GPT-5.5 Pro:
- Constructed explicit counterexample colourings showing that no such pair $(f, k)$ exists.

## Formalization Details

- **Target File:** `JSP_000788.lean`
- **Underlying Formalization:** `Erdos948.lean`
- **Main Theorem:**
  ```lean
  theorem jsp_000788_solved :
      ¬ (∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
        ∀ colouring : ℤ → Fin k,
          ∃ a : ℕ → ℤ, StrictMono a ∧
            {n | a n < (f n : ℤ)}.Infinite ∧
            ∃ omitted : Fin k, ∀ I : Finset ℕ,
              colouring (∑ i ∈ I, a i) ≠ omitted) :=
    Erdos948.not_erdos_948
  ```
- **Axioms Check:**
  `#print axioms jsp_000788_solved` depends strictly on standard foundational Lean axioms:
  ```lean
  [propext, Classical.choice, Quot.sound]
  ```
  Zero `sorry`, zero `admit`, zero custom axioms.

## Build & Verification Instructions

### Toolchain
- **Lean:** `leanprover/lean4:v4.33.0`
- **Mathlib:** `v4.33.0`

### Build
```bash
lake exe cache get
lake build
```

## Attribution & Provenance
- **Mathematical Solution:** Lisa Price and GPT-5.5 Pro (negative answer).
- **Formal Authors:** Codex, GPT-5.6 Sol, with upstream formalization in `plby/lean-proofs` (`src/latest/ErdosProblems/Erdos948.lean`).
- **Packaging & Verification:** Maintained and verified by 赵钦 (Qin Zhao, GitHub: [@Drag0ndddd1118](https://github.com/Drag0ndddd1118)).
