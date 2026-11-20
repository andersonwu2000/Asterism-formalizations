import ACS12.JointSharpGapMotion

/-! Complete moment identities for the original signed integration-by-parts terms. -/
namespace ACS12.GammaMeasure

open MeasureTheory Set Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)

private noncomputable def momentPower (p : ℝ) (k : ℕ) (s : ℝ) : ℝ := lineDensity p s * s ^ k
private noncomputable def momentX (s : ℝ) : ℝ := Real.exp (-s)

private noncomputable def momentB (p : ℝ) (k m : ℕ) (s : ℝ) : ℝ :=
  momentPower p k s * (momentX s ^ m / (1 - momentX s))

private noncomputable def momentD (p : ℝ) (k m : ℕ) (s : ℝ) : ℝ :=
  momentPower p k s * (momentX s ^ m / (1 - momentX s) ^ 2)

private noncomputable def momentE (p : ℝ) (k m : ℕ) (s : ℝ) : ℝ :=
  momentPower p k s * momentX s ^ m

noncomputable def momentBValue (p : ℝ) (k m : ℕ) : ℝ :=
  Real.Gamma (p + k) / Real.Gamma p * powerTail (p + k) m

noncomputable def momentDValue (p : ℝ) (k m : ℕ) : ℝ :=
  Real.Gamma (p + k) / Real.Gamma p *
    (powerTail (p + k - 1) m - ((m : ℝ) - 1) * powerTail (p + k) m)

noncomputable def momentEValue (p : ℝ) (k m : ℕ) : ℝ :=
  Real.Gamma (p + k) / Real.Gamma p * (m : ℝ) ^ (-(p + k))

private theorem momentPower_eq {p s : ℝ} (hs : 0 < s) (k : ℕ) :
    momentPower p k s = (Real.Gamma p)⁻¹ * s ^ (p + k - 1) := by
  unfold momentPower lineDensity
  rw [← Real.rpow_natCast,div_eq_mul_inv,mul_comm (s ^ (p - 1)),mul_assoc,← Real.rpow_add hs]
  congr 2
  ring

private theorem momentB_integral {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 1 ≤ k) (hm : 0 < m) :
    IntegrableOn (momentB p k m) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, momentB p k m s) = momentBValue p k m := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 < p + (k : ℝ) - 1 := by linarith only [hp,hK]
  have hF (s : ℝ) (hs : 0 < s) : momentB p k m s = (Real.Gamma p)⁻¹ *
      (s ^ (p + k - 1) * (Real.exp (-s * (m : ℝ)) / (1 - Real.exp (-s)))) := by
    rw [momentB,momentPower_eq hs,momentX,← Real.exp_nat_mul,mul_comm (m : ℝ),mul_assoc]
  constructor
  · apply ((boseMoment_integrable hr hm).const_mul _).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hF s hs).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hF s hs),integral_const_mul,
      boseMoment_integral hr hm,sub_add_cancel,momentBValue]
    ring

private theorem momentD_integral {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) :
    IntegrableOn (momentD p k m) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, momentD p k m s) = momentDValue p k m := by
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 1 < p + (k : ℝ) - 1 := by linarith only [hp,hK]
  have hF (s : ℝ) (hs : 0 < s) : momentD p k m s = (Real.Gamma p)⁻¹ *
      (s ^ (p + k - 1) * (Real.exp (-s * (m : ℝ)) / (1 - Real.exp (-s)) ^ 2)) := by
    rw [momentD,momentPower_eq hs,momentX,← Real.exp_nat_mul,mul_comm (m : ℝ),mul_assoc]
  constructor
  · apply ((boseSquaredMoment_integrable hr hm).const_mul _).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hF s hs).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hF s hs),integral_const_mul,
      boseSquaredMoment_integral hr hm,sub_add_cancel,momentDValue]
    ring

private theorem momentE_integral {p : ℝ} (hp : 0 < p) (k : ℕ) {m : ℕ} (hm : 0 < m) :
    IntegrableOn (momentE p k m) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, momentE p k m s) = momentEValue p k m := by
  obtain ⟨hI,hE⟩ := lineDensity_moment hp (Nat.cast_pos.mpr (show 0 < m from hm)) k
  have hF (s : ℝ) : momentE p k m s = lineDensity p s * s ^ k * Real.exp (-s * (m : ℝ)) := by
    rw [momentE,momentPower,momentX,← Real.exp_nat_mul,mul_comm (m : ℝ)]
  exact ⟨hI.congr (Eventually.of_forall (fun s => (hF s).symm)), by simp_rw [hF]; exact hE⟩

private theorem C_decay_form {s : ℝ} (hs : 0 < s) :
    BoseShape.C s = ((s - 1) * momentX s + momentX s ^ 2) / (1 - momentX s) ^ 2 := by
  let x := momentX s
  have hX : 0 < x := Real.exp_pos _
  have hE : Real.exp s = x⁻¹ := by unfold x momentX; rw [Real.exp_neg,inv_inv]
  have hD : 1 - x ≠ 0 := (expHead_den_pos hs).ne'
  unfold BoseShape.C
  rw [hE]
  change ((s - 1) * x⁻¹ + 1) / (x⁻¹ - 1) ^ 2 = ((s - 1) * x + x ^ 2) / (1 - x) ^ 2
  have hD' : x⁻¹ - 1 ≠ 0 := by rw [← hE]; exact (expTail_den_pos hs).ne'
  field_simp [hX.ne',hD,hD']

private noncomputable def sharpAC (p : ℝ) (k m : ℕ) (s : ℝ) : ℝ :=
  momentE p k m s * polyA s * BoseShape.C s

private noncomputable def sharpC (p : ℝ) (m : ℕ) (s : ℝ) : ℝ := momentE p 2 (m + 1) s * BoseShape.C s

private theorem sharpAC_eq {p s : ℝ} (hs : 0 < s) (k m : ℕ) :
    sharpAC p k m s = momentB p (k + 1) (m + 1) s + momentB p (k + 1) (m + 2) s -
      momentE p k (m + 1) s - momentD p (k + 2) (m + 2) s := by
  let x := momentX s
  have hX : 1 - x ≠ 0 := (expHead_den_pos hs).ne'
  unfold sharpAC momentE momentB momentD momentPower
  rw [C_decay_form hs,polyA]
  change lineDensity p s * s ^ k * x ^ m * (1 - (1 + s) * x) *
    (((s - 1) * x + x ^ 2) / (1 - x) ^ 2) =
      lineDensity p s * s ^ (k + 1) * (x ^ (m + 1) / (1 - x)) +
      lineDensity p s * s ^ (k + 1) * (x ^ (m + 2) / (1 - x)) -
      lineDensity p s * s ^ k * x ^ (m + 1) -
      lineDensity p s * s ^ (k + 2) * (x ^ (m + 2) / (1 - x) ^ 2)
  simp only [pow_succ,pow_zero,one_mul]
  field_simp [hX]
  ring

private theorem sharpC_eq {p s : ℝ} (hs : 0 < s) (m : ℕ) :
    sharpC p m s = momentD p 3 (m + 2) s - momentB p 2 (m + 2) s := by
  let x := momentX s
  have hX : 1 - x ≠ 0 := (expHead_den_pos hs).ne'
  unfold sharpC momentE momentD momentB momentPower
  rw [C_decay_form hs]
  change lineDensity p s * s ^ 2 * x ^ (m + 1) * (((s - 1) * x + x ^ 2) / (1 - x) ^ 2) =
    lineDensity p s * s ^ 3 * (x ^ (m + 2) / (1 - x) ^ 2) -
    lineDensity p s * s ^ 2 * (x ^ (m + 2) / (1 - x))
  simp only [pow_succ,pow_zero,one_mul]
  field_simp [hX]
  ring

noncomputable def sharpACValue (p : ℝ) (k m : ℕ) : ℝ :=
  momentBValue p (k + 1) (m + 1) + momentBValue p (k + 1) (m + 2) -
    momentEValue p k (m + 1) - momentDValue p (k + 2) (m + 2)

noncomputable def sharpCValue (p : ℝ) (m : ℕ) : ℝ :=
  momentDValue p 3 (m + 2) - momentBValue p 2 (m + 2)

private theorem sharpAC_integral {p : ℝ} (hp : 0 < p) (k m : ℕ) :
    IntegrableOn (sharpAC p k m) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, sharpAC p k m s) = sharpACValue p k m := by
  obtain ⟨hA,hAE⟩ := momentB_integral hp (k := k + 1) (m := m + 1) (by omega) (by omega)
  obtain ⟨hB,hBE⟩ := momentB_integral hp (k := k + 1) (m := m + 2) (by omega) (by omega)
  obtain ⟨hE,hEE⟩ := momentE_integral hp k (m := m + 1) (by omega)
  obtain ⟨hD,hDE⟩ := momentD_integral hp (k := k + 2) (m := m + 2) (by omega) (by omega)
  constructor
  · apply (((hA.add hB).sub hE).sub hD).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (sharpAC_eq hs k m).symm
  · let A := momentB p (k + 1) (m + 1)
    let B := momentB p (k + 1) (m + 2)
    let E := momentE p k (m + 1)
    let D := momentD p (k + 2) (m + 2)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => sharpAC_eq hs k m)]
    calc
      _ = (∫ s in Ioi 0, A s + B s - E s) - ∫ s in Ioi 0, D s := integral_sub ((hA.add hB).sub hE) hD
      _ = ((∫ s in Ioi 0, A s + B s) - ∫ s in Ioi 0, E s) - ∫ s in Ioi 0, D s := by
        rw [show (∫ s in Ioi 0, A s + B s - E s) = (∫ s in Ioi 0, A s + B s) - ∫ s in Ioi 0, E s
          from integral_sub (hA.add hB) hE]
      _ = _ := by
        unfold A B E D
        rw [integral_add hA hB,hAE,hBE,hEE,hDE,sharpACValue]

private theorem sharpC_integral {p : ℝ} (hp : 0 < p) (m : ℕ) :
    IntegrableOn (sharpC p m) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, sharpC p m s) = sharpCValue p m := by
  obtain ⟨hD,hDE⟩ := momentD_integral hp (k := 3) (m := m + 2) (by decide) (by omega)
  obtain ⟨hB,hBE⟩ := momentB_integral hp (k := 2) (m := m + 2) (by decide) (by omega)
  constructor
  · apply (hD.sub hB).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (sharpC_eq hs m).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => sharpC_eq hs m),
      integral_sub hD hB,hDE,hBE,sharpCValue]

theorem sharpGapMoment_exact {p : ℝ} (hp : 0 < p) (m : ℕ)
    (hI : IntegrableOn (fun s => lineDensity p s * Real.exp (-s * (m : ℝ)) *
      polyA s * s * (-BoseShape.C₁ s)) (Ioi 0)) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * (m : ℝ)) *
      polyA s * s * (-BoseShape.C₁ s)) =
      p * sharpACValue p 0 m - (m : ℝ) * sharpACValue p 1 m + sharpCValue p m := by
  let A (s : ℝ) := p * sharpAC p 0 m s
  let B (s : ℝ) := (m : ℝ) * sharpAC p 1 m s
  let C := sharpC p m
  let K (s : ℝ) := lineDensity p s * Real.exp (-s * (m : ℝ)) * polyA s * s * (-BoseShape.C₁ s)
  have hD (s : ℝ) : sharpGapDerivative p (m : ℝ) s = A s - B s + C s - K s := by
    unfold sharpGapDerivative A B C K sharpAC sharpC momentE momentPower momentX
    simp only [pow_zero,pow_one,mul_one,← Real.exp_nat_mul,Nat.cast_add,Nat.cast_one,mul_comm (m : ℝ) (-s),
      mul_comm ((m : ℝ) + 1) (-s)]
  obtain ⟨hA,hAE⟩ := sharpAC_integral hp 0 m
  obtain ⟨hB,hBE⟩ := sharpAC_integral hp 1 m
  obtain ⟨hC,hCE⟩ := sharpC_integral hp m
  have hAi : IntegrableOn A (Ioi 0) := hA.const_mul p
  have hBi : IntegrableOn B (Ioi 0) := hB.const_mul (m : ℝ)
  have hCi : IntegrableOn C (Ioi 0) := hC
  have hKi : IntegrableOn K (Ioi 0) := hI
  have hJ : IntegrableOn (sharpGapDerivative p (m : ℝ)) (Ioi 0) :=
    (((hAi.sub hBi).add hCi).sub hKi).congr (Eventually.of_forall fun s => (hD s).symm)
  have h := sharpGapDerivative_integral_zero hp (Nat.cast_nonneg m) hJ
  simp_rw [hD] at h
  have hInt : (∫ s : ℝ in Ioi 0, A s - B s + C s - K s) =
      (∫ s in Ioi 0, A s) - (∫ s in Ioi 0, B s) + (∫ s in Ioi 0, C s) - ∫ s in Ioi 0, K s := by
    calc
      _ = (∫ s in Ioi 0, A s - B s + C s) - ∫ s in Ioi 0, K s := integral_sub ((hAi.sub hBi).add hCi) hKi
      _ = ((∫ s in Ioi 0, A s - B s) + ∫ s in Ioi 0, C s) - ∫ s in Ioi 0, K s := by
        rw [show (∫ s in Ioi 0, A s - B s + C s) = (∫ s in Ioi 0, A s - B s) + ∫ s in Ioi 0, C s
          from integral_add (hAi.sub hBi) hCi]
      _ = _ := by rw [integral_sub hAi hBi]
  rw [hInt] at h
  dsimp only [A,B] at h
  rw [integral_const_mul,integral_const_mul,hAE,hBE] at h
  change p * sharpACValue p 0 m - (m : ℝ) * sharpACValue p 1 m + (∫ s in Ioi 0, sharpC p m s) -
    (∫ s in Ioi 0, K s) = 0 at h
  rw [hCE] at h
  exact eq_of_sub_eq_zero h |>.symm

end ACS12.GammaMeasure
