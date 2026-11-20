import CenteredCircle.IntegralProductComparison

/-! Positive parts of signed Laplace transforms with an ordered multiplier. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

private theorem monotone_product_test {w q f : ℝ → ℝ}
    (hw : IntegrableOn w (Ioi 0))
    (hq : IntegrableOn (fun s => w s * q s) (Ioi 0))
    (hf : IntegrableOn (fun s => w s * f s) (Ioi 0))
    (hprod : IntegrableOn (fun s => w s * q s * f s) (Ioi 0))
    (hwpos : ∀ s > 0, 0 < w s) (hf₀ : ∀ s > 0, 0 ≤ f s)
    (hQ : MonotoneOn q (Ioi 0)) (hF : MonotoneOn f (Ioi 0))
    (hq₀ : 0 ≤ ∫ s : ℝ in Ioi 0, w s * q s) :
    0 ≤ ∫ s : ℝ in Ioi 0, w s * q s * f s := by
  have h := integral_product_comparison hprod hw hq hf ?_
  · have hPos : 0 < ∫ s : ℝ in Ioi 0, w s := by
      letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
      have hI := integral_strict_of_ae_lt (volume.restrict (Ioi (0 : ℝ))) (integrable_zero ℝ ℝ _) hw ?_
      · simpa only [integral_zero] using hI
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hwpos s hs
    have hF₀ : 0 ≤ ∫ s : ℝ in Ioi 0, w s * f s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (hwpos s hs).le (hf₀ s hs)
    by_contra! hneg
    exact (not_lt_of_ge ((mul_nonneg hq₀ hF₀).trans h)) (mul_neg_of_neg_of_pos hneg hPos)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hE : (w x * q x * f x) * w y + (w y * q y * f y) * w x -
        (w x * q x) * (w y * f y) - (w y * q y) * (w x * f x) =
        (w x * w y) * ((q x - q y) * (f x - f y)) := by ring
    rw [hE]
    apply mul_nonneg (mul_nonneg (hwpos x hx).le (hwpos y hy).le)
    rcases le_total x y with hxy | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hQ hx hy hxy))
        (sub_nonpos.mpr (hF hx hy hxy))
    · exact mul_nonneg (sub_nonneg.mpr (hQ hy hx hyx)) (sub_nonneg.mpr (hF hy hx hyx))

theorem weightedPositivePart_antitone {G : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (hW : ∀ t > 0, IntegrableOn (W t) (Ioi 0))
    (hQ : ∀ t > 0, IntegrableOn (fun s => W t s * q s) (Ioi 0))
    (hRep : ∀ t > 0, G t = ∫ s : ℝ in Ioi 0, W t s * q s)
    (hPos : ∀ t s, 0 < s → 0 < W t s)
    (hTilt : ∀ t x s, W t s * Real.exp (s * (t - x)) = W x s)
    (hMono : MonotoneOn q (Ioi 0)) :
    AntitoneOn (fun t => max 0 (G t)) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  change max 0 (G y) ≤ max 0 (G x)
  by_cases h : 0 ≤ G y
  · rw [max_eq_right h]
    apply le_max_of_le_right
    let w := W y
    let f (s : ℝ) := Real.exp (s * (y - x)) - 1
    have hfE (s : ℝ) : w s * f s = W x s - w s := by
      change W y s * (Real.exp (s * (y - x)) - 1) =
        W x s - W y s
      rw [mul_sub (W y s), mul_one, hTilt]
    have hqE (s : ℝ) : w s * q s * f s =
        W x s * q s - w s * q s := by
      rw [mul_right_comm, hfE, sub_mul]
    have hw : IntegrableOn w (Ioi 0) := hW y hy
    have hqX := hQ x hx
    have hqY := hQ y hy
    have hfI := ((hW x hx).sub hw).congr (Eventually.of_forall fun s =>
      (hfE s).symm)
    have hI := (hqX.sub hqY).congr (Eventually.of_forall fun s => (hqE s).symm)
    have hfPos (s : ℝ) (hs : 0 < s) : 0 ≤ f s :=
      sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hs.le (sub_nonneg.mpr hxy)))
    have hfMono : MonotoneOn f (Ioi 0) := by
      intro s hs t ht hst
      exact sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hxy))) _
    have hnon := monotone_product_test hw hqY hfI hI (fun s hs => hPos y s hs)
      hfPos hMono hfMono ((hRep y hy) ▸ h)
    have hSum : (∫ s : ℝ in Ioi 0, w s * q s * f s) =
        G x - G y := by
      simp_rw [hqE]
      exact (integral_sub hqX hqY).trans (by rw [hRep x hx, hRep y hy])
    exact sub_nonneg.mp (hSum ▸ hnon)
  · rw [max_eq_left (le_of_not_ge h)]
    exact le_max_left _ _

private noncomputable def blendTilt (c d δ s : ℝ) : ℝ :=
  c * Real.exp (s * (d * δ)) + d * Real.exp (s * (-c * δ)) - 1

private theorem blendTilt_nonneg {c d : ℝ} (hC : 0 ≤ c) (hD : 0 ≤ d)
    (hCD : c + d = 1) (δ s : ℝ) : 0 ≤ blendTilt c d δ s := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s * (d * δ))) hC
  have h₂ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s * (-c * δ))) hD
  unfold blendTilt
  nlinarith only [h₁, h₂, hCD]

private theorem blendTilt_mono {c d : ℝ} (hC : 0 ≤ c) (hD : 0 ≤ d) (δ : ℝ) :
    MonotoneOn (blendTilt c d δ) (Ioi 0) := by
  have hDer (s : ℝ) : HasDerivAt (blendTilt c d δ)
      (c * d * δ * (Real.exp (s * (d * δ)) - Real.exp (s * (-c * δ)))) s := by
    have h₁ := (((hasDerivAt_id s).mul_const (d * δ)).exp).const_mul c
    have h₂ := (((hasDerivAt_id s).mul_const (-c * δ)).exp).const_mul d
    convert (h₁.add h₂).sub_const 1 using 1
    dsimp only [id_eq, one_mul]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · exact fun s _ => (hDer s).continuousAt.continuousWithinAt
  · exact fun s _ => (hDer s).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs₀ : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
    rw [(hDer s).deriv, mul_assoc (c * d)]
    apply mul_nonneg (mul_nonneg hC hD)
    by_cases hδ : 0 ≤ δ
    · apply mul_nonneg hδ
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by
        have h₁ := mul_nonneg hD hδ
        have h₂ := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) hδ
        exact mul_le_mul_of_nonneg_left (h₂.trans h₁) hs₀.le))
    · have hδ₀ : δ ≤ 0 := (lt_of_not_ge hδ).le
      apply mul_nonneg_of_nonpos_of_nonpos hδ₀
      exact sub_nonpos.mpr (Real.exp_le_exp.mpr (by
        have h₁ := mul_nonpos_of_nonneg_of_nonpos hD hδ₀
        have h₂ := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hC) hδ₀
        exact mul_le_mul_of_nonneg_left (h₁.trans h₂) hs₀.le))

theorem weightedPositivePart_convex {G : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (hW : ∀ t > 0, IntegrableOn (W t) (Ioi 0))
    (hQ : ∀ t > 0, IntegrableOn (fun s => W t s * q s) (Ioi 0))
    (hRep : ∀ t > 0, G t = ∫ s : ℝ in Ioi 0, W t s * q s)
    (hPos : ∀ t s, 0 < s → 0 < W t s)
    (hTilt : ∀ t x s, W t s * Real.exp (s * (t - x)) = W x s)
    (hMono : MonotoneOn q (Ioi 0)) :
    ConvexOn ℝ (Ioi 0) (fun t => max 0 (G t)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  simp only [smul_eq_mul]
  let t := c * x + d * y
  have ht : 0 < t := convex_Ioi (0 : ℝ) hx hy hc hd hcd
  change max 0 (G t) ≤ c * max 0 (G x) + d * max 0 (G y)
  by_cases hGt : 0 ≤ G t
  · rw [max_eq_right hGt]
    refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hc)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hd))
    let w := W t
    let f := blendTilt c d (y - x)
    have htX : t - x = d * (y - x) := by
      dsimp only [t]
      linear_combination x * hcd
    have htY : t - y = -c * (y - x) := by
      dsimp only [t]
      linear_combination y * hcd
    have hfE (s : ℝ) : w s * f s = c * W x s + d * W y s - w s := by
      change w s * (c * Real.exp (s * (d * (y - x))) +
        d * Real.exp (s * (-c * (y - x))) - 1) = _
      rw [← htX, ← htY, mul_sub (w s), mul_add (w s), mul_one, mul_left_comm (w s) c,
        mul_left_comm (w s) d]
      dsimp only [w]
      rw [hTilt, hTilt]
    have hqE (s : ℝ) : w s * q s * f s =
        c * (W x s * q s) + d * (W y s * q s) - w s * q s := by
      rw [mul_right_comm, hfE]
      ring
    have hw : IntegrableOn w (Ioi 0) := hW t ht
    have hqX := hQ x hx₀
    have hqY := hQ y hy₀
    have hqT := hQ t ht
    have hfI := ((((hW x hx₀).const_mul c).add
      ((hW y hy₀).const_mul d)).sub hw).congr
      (Eventually.of_forall fun s => (hfE s).symm)
    have hI := (((hqX.const_mul c).add (hqY.const_mul d)).sub hqT).congr
      (Eventually.of_forall fun s => (hqE s).symm)
    have hNon := monotone_product_test hw hqT hfI hI
      (fun _ hs => hPos t _ hs) (fun s _ => blendTilt_nonneg hc hd hcd (y - x) s)
      hMono (blendTilt_mono hc hd (y - x))
      ((hRep t ht) ▸ hGt)
    have hSum : (∫ s : ℝ in Ioi 0, w s * q s * f s) = c * G x + d * G y - G t := by
      simp_rw [hqE]
      calc
        _ = (∫ s : ℝ in Ioi 0, c * (W x s * q s) +
              d * (W y s * q s)) -
            ∫ s : ℝ in Ioi 0, w s * q s :=
          integral_sub ((hqX.const_mul c).add (hqY.const_mul d)) hqT
        _ = _ := by
          rw [integral_add (hqX.const_mul c) (hqY.const_mul d), integral_const_mul, integral_const_mul]
          simp only [hRep x hx₀, hRep y hy₀, hRep t ht, w]
    exact sub_nonneg.mp (hSum ▸ hNon)
  · rw [max_eq_left (le_of_not_ge hGt)]
    exact add_nonneg (mul_nonneg hc (le_max_left _ _)) (mul_nonneg hd (le_max_left _ _))

end ACS12.GammaMeasure
