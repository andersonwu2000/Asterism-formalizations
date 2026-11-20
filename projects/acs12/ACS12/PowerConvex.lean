import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ACS12

open Set

theorem negativePower_convex {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-s)) := by
  have h₁ (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => x ^ (-s)) (-s * x ^ (-s - 1)) x := by
    simpa only [id_eq,one_mul,mul_one] using
      (hasDerivAt_id x).rpow_const (p := -s) (Or.inl hx.ne')
  have h₂ (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => -s * x ^ (-s - 1)) ((s * (s + 1)) * x ^ (-s - 2)) x := by
    convert (((hasDerivAt_id x).rpow_const (p := -s - 1) (Or.inl hx.ne')).const_mul (-s)) using 1
    simp only [id_eq,show -s - 1 - 1 = -s - 2 by ring]
    ring
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi _)
    (fun x hx => (h₁ x hx).continuousAt.continuousWithinAt)
    (fun x hx => (h₁ x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => (h₂ x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => by have hx₀ : 0 < x := interior_subset hx; positivity)

end ACS12
