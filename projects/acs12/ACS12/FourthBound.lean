import ACS12.FourthDensity

/-! Uniform integrable envelopes for the fourth-source derivatives. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

private theorem expRate_le {s c d : ℝ} (hs : 0 < s) (hcd : c ≤ d) :
    Real.exp (-s * d) ≤ Real.exp (-s * c) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcd (neg_nonpos.mpr hs.le))

theorem fourthV_bound {u v r m V R M c s : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hr : 0 < r) (hs : 0 < s) (hcU : c ≤ u) (hcV : c ≤ v)
    (hvV : v ≤ V) (hrR : r ≤ R) (hm : |m| ≤ M) :
    |fourthV u v r m s| ≤ (u + 1 + (V * (1 + R) + M)) *
      (1 + s + s ^ 2) * Real.exp (-s * c) := by
  let P := 1 + s + s ^ 2
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP₁ : 1 ≤ P := le_add_of_nonneg_right (sq_nonneg s) |>.trans' (le_add_of_nonneg_right hs.le)
  have hPs : s ≤ P := le_add_of_nonneg_right (sq_nonneg s) |>.trans' (le_add_of_nonneg_left zero_le_one)
  have hPs₂ : s ^ 2 ≤ P := le_add_of_nonneg_left (by positivity)
  have hV₀ : 0 ≤ V := hv.le.trans hvV
  have hR₀ : 0 ≤ R := hr.le.trans hrR
  have hM₀ : 0 ≤ M := (abs_nonneg m).trans hm
  have hβ : 0 < scaledExpTail s 1 := div_pos zero_lt_one
    (expTail_den_pos (by simpa only [mul_one] using hs))
  have hβB : s * scaledExpTail s 1 ≤ 1 := by
    rw [scaledExpTail_eq_factor hs, mul_div_cancel₀ _ hs.ne', mul_one]
    exact (BoseShape.expTail_bounds hs).2
  have hY : 0 < 1 - Real.exp (-s * v) := by
    simpa only [neg_mul] using expHead_den_pos (mul_pos hs hv)
  have hY₁ : 1 - Real.exp (-s * v) ≤ 1 := sub_le_self _ (Real.exp_pos _).le
  have hT₀ : 0 ≤ fourthFirstStream u s := mul_nonneg (Real.exp_pos _).le (add_nonneg hu.le hβ.le)
  have hFirst : s * (1 - Real.exp (-s * v)) * fourthFirstStream u s ≤
      (u + 1) * P * Real.exp (-s * c) := by
    calc
      _ ≤ s * fourthFirstStream u s :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hs.le hY₁) hT₀
      _ = (u * s + s * scaledExpTail s 1) * Real.exp (-s * u) := by
        unfold fourthFirstStream
        ring
      _ ≤ (u * s + 1) * Real.exp (-s * u) :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl hβB) (Real.exp_pos _).le
      _ ≤ (u + 1) * P * Real.exp (-s * c) := by
        have hU := add_le_add (mul_le_mul_of_nonneg_left hPs hu.le) hP₁
        have hU' : u * s + 1 ≤ (u + 1) * P := by nlinarith only [hU]
        exact mul_le_mul hU' (expRate_le hs hcU) (Real.exp_pos _).le (mul_nonneg (by positivity) hP)
  have hHead₀ : 0 ≤ expHeadFactor (r * s) :=
    (div_pos (mul_pos hr hs) (expHead_den_pos (mul_pos hr hs))).le
  have hHead : expHeadFactor (r * s) ≤ 1 + R * s := by
    rw [expHeadFactor_eq_add_expTail (mul_pos hr hs)]
    have h := add_le_add (mul_le_mul_of_nonneg_right hrR hs.le) (BoseShape.expTail_bounds (mul_pos hr hs)).2
    linarith
  have hCore : |v * s * expHeadFactor (r * s) - m * s| ≤ (V * (1 + R) + M) * P := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hv.le hs.le) hHead₀),
      abs_mul, abs_of_pos hs]
    calc
      _ ≤ V * s * (1 + R * s) + M * s :=
        add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right hvV hs.le) hHead hHead₀
          (mul_nonneg hV₀ hs.le)) (mul_le_mul_of_nonneg_right hm hs.le)
      _ = V * s + (V * R) * s ^ 2 + M * s := by ring
      _ ≤ V * P + (V * R) * P + M * P := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hPs hV₀)
          (mul_le_mul_of_nonneg_left hPs₂ (mul_nonneg hV₀ hR₀)))
        (mul_le_mul_of_nonneg_left hPs hM₀)
      _ = _ := by ring
  unfold fourthV
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hs.le hY.le) hT₀),
    abs_mul (Real.exp (-s * v)), abs_of_pos (Real.exp_pos _)]
  have hTail := mul_le_mul (expRate_le hs hcV) hCore (abs_nonneg _)
    (Real.exp_pos (-s * c)).le
  refine (add_le_add hFirst hTail).trans_eq ?_
  ring

theorem fourthD_bound {v r V R c s : ℝ} (hv : 0 < v) (hr : 0 < r) (hs : 0 < s)
    (hcV : c ≤ v) (hcR : c ≤ r) (hvV : v ≤ V) (hrR : r ≤ R) :
    |fourthD v r s| ≤ (1 + V + BoseShape.decayConstant * (R + 1)) *
      (1 + s + s ^ 2) * Real.exp (-s * c) := by
  let P := 1 + s + s ^ 2
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP₁ : 1 ≤ P := le_add_of_nonneg_right (sq_nonneg s) |>.trans' (le_add_of_nonneg_right hs.le)
  have hPs : s ≤ P := le_add_of_nonneg_right (sq_nonneg s) |>.trans' (le_add_of_nonneg_left zero_le_one)
  have hV₀ : 0 ≤ V := hv.le.trans hvV
  have hR₀ : 0 ≤ R := hr.le.trans hrR
  have hB : polyA (v * s) ≤ 1 := by
    unfold polyA
    exact sub_le_self _ (mul_nonneg (by positivity) (Real.exp_pos _).le)
  have hX : 1 + v * s ≤ (1 + V) * P := by
    have h := add_le_add hP₁ ((mul_le_mul_of_nonneg_right hvV hs.le).trans
      (mul_le_mul_of_nonneg_left hPs hV₀))
    nlinarith only [h]
  have hY : r * s + 1 ≤ (R + 1) * P := by
    have h := add_le_add ((mul_le_mul_of_nonneg_right hrR hs.le).trans
      (mul_le_mul_of_nonneg_left hPs hR₀)) hP₁
    nlinarith only [h]
  have hC : BoseShape.C (r * s) ≤ BoseShape.decayConstant * ((R + 1) * P) * Real.exp (-s * c) := by
    refine (BoseShape.C_le_decay (mul_pos hr hs)).trans ?_
    have he : Real.exp (-(r * s)) ≤ Real.exp (-s * c) := by
      rw [mul_comm r s]
      simpa only [neg_mul] using expRate_le hs hcR
    exact mul_le_mul (mul_le_mul_of_nonneg_left hY BoseShape.decayConstant_pos.le) he
      (Real.exp_pos _).le (mul_nonneg BoseShape.decayConstant_pos.le (mul_nonneg (by linarith) hP))
  rw [abs_of_pos (fourthD_pos hv hr hs), fourthD]
  have hFirst := mul_le_mul (expRate_le hs hcV) hX (show 0 ≤ 1 + v * s by positivity)
    (Real.exp_pos (-s * c)).le
  have hSecond := (mul_le_of_le_one_left (BoseShape.C_pos (mul_pos hr hs)).le hB).trans hC
  refine (add_le_add hFirst hSecond).trans_eq ?_
  ring

theorem fourth_direction_bound {u v r m V R M c s dv dr dm : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : 0 < r) (hs : 0 < s)
    (hcU : c ≤ u) (hcV : c ≤ v) (hcR : c ≤ r) (hvV : v ≤ V) (hrR : r ≤ R) (hm : |m| ≤ M) :
    |dv * fourthV u v r m s - dr * fourthD v r s + dm * Real.exp (-s * v)| ≤
      (|dv| * (u + 1 + (V * (1 + R) + M)) +
       |dr| * (1 + V + BoseShape.decayConstant * (R + 1)) + |dm|) *
      (1 + s + s ^ 2) * Real.exp (-s * c) := by
  let P := 1 + s + s ^ 2
  have hP₁ : 1 ≤ P := le_add_of_nonneg_right (sq_nonneg s) |>.trans' (le_add_of_nonneg_right hs.le)
  have hExp : Real.exp (-s * v) ≤ P * Real.exp (-s * c) :=
    (expRate_le hs hcV).trans (le_mul_of_one_le_left (Real.exp_pos _).le hP₁)
  calc
    _ ≤ |dv * fourthV u v r m s| + |dr * fourthD v r s| + |dm * Real.exp (-s * v)| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ |dv| * ((u + 1 + (V * (1 + R) + M)) * P * Real.exp (-s * c)) +
          |dr| * ((1 + V + BoseShape.decayConstant * (R + 1)) * P * Real.exp (-s * c)) +
          |dm| * (P * Real.exp (-s * c)) := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos (-s * v))]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left
        (fourthV_bound hu hv hr hs hcU hcV hvV hrR hm) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (fourthD_bound hv hr hs hcV hcR hvV hrR) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hExp (abs_nonneg _))
    _ = _ := by dsimp only [P]; ring

theorem integrable_cubic_exp_envelope {c : ℝ} (hc : 0 < c) (D : ℝ) :
    IntegrableOn (fun s : ℝ => D * (1 + s) * (1 + s + s ^ 2) * Real.exp (-s * c)) (Ioi 0) := by
  have h0 := expMoment_nat_integrable 0 hc
  have h1 := (expMoment_nat_integrable 1 hc).const_mul 2
  have h2 := (expMoment_nat_integrable 2 hc).const_mul 2
  have h3 := expMoment_nat_integrable 3 hc
  refine ((((h0.add h1).add h2).add h3).const_mul D).congr (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, pow_zero, pow_one, one_mul]
  ring

end ACS12.GammaMeasure

