import ACS12.PureZetaEnvelope
import ACS12.PurePeano

/-! Directed finite prefixes at the two source endpoints. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN
open scoped BigOperators

private theorem fifth_upper {b x : ℝ} {k : ℕ} (hb : 0 < b) (hx : 0 ≤ x)
    (h : (b ^ k)⁻¹ < x ^ 5) : b ^ (-(k : ℝ) / 5) < x :=
  fifth_rpow_upper hb hx h

private theorem pureA_atom_le {τ x A B C : ℝ} (hτ : 0 ≤ τ)
    (hA : x ^ (-(9 : ℝ) / 5) ≤ A) (hB : B ≤ (x + 1) ^ (-(9 : ℝ) / 5))
    (hC : C ≤ (x + 1) ^ (-(14 : ℝ) / 5)) :
    τ * purePeanoA (9 / 5) 1 x ≤ τ * (A - B - (9 / 5) * C) := by
  apply mul_le_mul_of_nonneg_left _ hτ
  unfold purePeanoA
  rw [show -((9 / 5 : ℝ) + 1) = -(14 : ℝ) / 5 by norm_num]
  simp only [one_mul]
  linarith only [hA, hB, hC]

private theorem pureB_atom_le {x A B C : ℝ}
    (hA : x ^ (-(14 : ℝ) / 5) ≤ A) (hB : B ≤ x ^ (-(9 : ℝ) / 5))
    (hC : (x + 7 / 8) ^ (-(9 : ℝ) / 5) ≤ C) :
    purePeanoB (9 / 5) (7 / 8) x ≤ (7 / 8) * (9 / 5) * A - B + C := by
  unfold purePeanoB
  rw [show -((9 / 5 : ℝ) + 1) = -(14 : ℝ) / 5 by norm_num]
  linarith only [hA, hB, hC]

noncomputable def aPrefixUpper (τ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, τ * purePeanoA (9 / 5) 1 (((j : ℝ) + 1) * τ)

noncomputable def bPrefixUpper : ℝ :=
  ∑ j ∈ Finset.range 6, purePeanoB (9 / 5) (7 / 8) ((j : ℝ) + 1)

theorem aPrefixUpper_zero_lt : aPrefixUpper (5 / 7) < 118 / 125 := by
  have h1 := pureA_atom_le (τ := 5 / 7) (x := 5 / 7) (A := 1832443/1000000) (B := 379009/1000000) (C := 221088/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h2 := pureA_atom_le (τ := 5 / 7) (x := 10 / 7) (A := 526232/1000000) (B := 202473/1000000) (C := 83371/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h3 := pureA_atom_le (τ := 5 / 7) (x := 15 / 7) (A := 253637/1000000) (B := 127296/1000000) (C := 40503/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h4 := pureA_atom_le (τ := 5 / 7) (x := 20 / 7) (A := 151121/1000000) (B := 88048/1000000) (C := 22827/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h5 := pureA_atom_le (τ := 5 / 7) (x := 25 / 7) (A := 101132/1000000) (B := 64849/1000000) (C := 14185/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h6 := pureA_atom_le (τ := 5 / 7) (x := 30 / 7) (A := 72839/1000000) (B := 49935/1000000) (C := 9447/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  norm_num [aPrefixUpper, Finset.sum_range_succ]
  linarith only [h1, h2, h3, h4, h5, h6]

theorem aPrefixUpper_edge_lt : aPrefixUpper (23 / 25) < 317 / 500 := by
  have h1 := pureA_atom_le (τ := 23 / 25) (x := 23 / 25) (A := 1161936/1000000) (B := 309070/1000000) (C := 160974/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h2 := pureA_atom_le (τ := 23 / 25) (x := 46 / 25) (A := 333679/1000000) (B := 152766/1000000) (C := 53790/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h3 := pureA_atom_le (τ := 23 / 25) (x := 69 / 25) (A := 160829/1000000) (B := 92185/1000000) (C := 24517/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h4 := pureA_atom_le (τ := 23 / 25) (x := 92 / 25) (A := 95824/1000000) (B := 62166/1000000) (C := 13283/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h5 := pureA_atom_le (τ := 23 / 25) (x := 23 / 5) (A := 64127/1000000) (B := 45005/1000000) (C := 8036/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  have h6 := pureA_atom_le (τ := 23 / 25) (x := 138 / 25) (A := 46186/1000000) (B := 34225/1000000) (C := 5249/1000000)
    (by norm_num) (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
  norm_num [aPrefixUpper, Finset.sum_range_succ]
  linarith only [h1, h2, h3, h4, h5, h6]

theorem bPrefixUpper_edge_lt : bPrefixUpper < 1021 / 1000 := by
  have h1 := pureB_atom_le (x := 1) (A := 1000001/1000000) (B := 999999/1000000) (C := 322552/1000000)
    (fifth_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  have h2 := pureB_atom_le (x := 2) (A := 143589/1000000) (B := 287173/1000000) (C := 149436/1000000)
    (fifth_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  have h3 := pureB_atom_le (x := 3) (A := 46140/1000000) (B := 138413/1000000) (C := 87321/1000000)
    (fifth_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  have h4 := pureB_atom_le (x := 4) (A := 20619/1000000) (B := 82468/1000000) (C := 57764/1000000)
    (fifth_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  have h5 := pureB_atom_le (x := 5) (A := 11039/1000000) (B := 55188/1000000) (C := 41286/1000000)
    (fifth_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  have h6 := pureB_atom_le (x := 6) (A := 6626/1000000) (B := 39748/1000000) (C := 31112/1000000)
    (fifth_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
    (fifth_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)).le
  norm_num [bPrefixUpper, Finset.sum_range_succ]
  linarith only [h1, h2, h3, h4, h5, h6]

end ACS12.GammaMeasure
