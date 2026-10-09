/-
  The Justin Sun Prize (孙宇晨奖) — JSP-000788

  **Submission.lean: top-level theorem and bridge.**

  This file bridges the underlying constructive Lean 4 formalization of Erdős
  Problem #948 to the statement of record in `Challenge.lean`.
-/

import Challenge
import Erdos948Colouring.Main

open JSP000788

/--
Top-level resolution theorem for JSP-000788 (Erdős Problem #948).
Proves `jsp000788Statement` by bridging from the greedy window colouring construction.
-/
theorem jsp_000788_solved : jsp000788Statement := by
  rintro ⟨f, k, hk, hbad⟩
  refine Erdos948.erdos_948_closed ⟨f, k, hk, fun c => ?_⟩
  obtain ⟨a, ha, hsmall, j, hj⟩ := hbad c
  exact ⟨a, ha, hsmall, j, fun m hm => hj m hm⟩

#print axioms jsp_000788_solved
