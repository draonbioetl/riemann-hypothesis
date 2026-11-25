module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Set Metric Filter Complex MeasureTheory Function Pi Finset Real intervalIntegral
open scoped Topology

namespace InjectiveHolomorphicJacobianNeZero

private lemma exists_mem_ne_of_mem_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] {U : Set E} {a : E} (hU : U ∈ 𝓝 a) : ∃ x ∈ U, x ≠ a :=
  (Eventually.and (nhdsWithin_le_nhds (s := {a}ᶜ) hU) self_mem_nhdsWithin).exists

private lemma one {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  let e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hne := InjectiveHolomorphicDerivNeZero.proof (e.symm ⁻¹' U) (⇑e ∘ f ∘ ⇑e.symm)
    (hU.preimage e.symm.continuous)
    (e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h ↦ h))
    (fun _ hs _ ht h ↦ e.symm.injective (hinj hs ht (e.injective h))) (e x) (by simpa using hx)
  have hx' : e.symm (e x) = x := e.symm_apply_apply x
  have hφx := e.hasFDerivAt.comp (e x)
    ((hx'.symm ▸ (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt).comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv, hx'] at hne
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_one, LinearMap.toMatrix'_apply]
  simpa [e, show (1 : Fin 1 → ℂ) = single 0 1 by ext i; fin_cases i; simp] using hne

/-- Directional derivatives of a holomorphic map between finite-dimensional complex normed spaces
are holomorphic, proved by differentiating the 1D Cauchy integral formula under the integral sign. -/
private lemma differentiableOn_fderiv_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x ↦ fderiv ℂ f x v) U := fun a ha ↦ by
  obtain ⟨r, hr, hU1⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds ha)
    ((hf.differentiableAt (hU.mem_nhds ha)).continuousAt.preimage_mem_nhds (ball_mem_nhds _ one_pos)))
  set s := r / (‖v‖ + 2)
  have hs : 0 < s := by positivity
  have hsr : s * (‖v‖ + 2) = r := div_mul_cancel₀ r (by positivity)
  have hsub {x} (hx : x ∈ ball a s) {ζ : ℂ} (hζ : ‖ζ‖ ≤ s) : ball (x + ζ • v) s ⊆ ball a r := fun z hz ↦ by
    have := dist_triangle4 z (x + ζ • v) x a
    simp only [dist_self_add_left, norm_smul, mem_ball] at *
    nlinarith [norm_nonneg v]
  have hm {x} (hx : x ∈ ball a s) {ζ : ℂ} (hζ : ‖ζ‖ ≤ s) := hU1 (hsub hx hζ (mem_ball_self hs))
  let γ : ℝ → ℂ := circleMap 0 s
  let c : ℝ → ℂ := fun θ ↦ (γ θ)⁻¹ * I
  have hc : Continuous c := by fun_prop (disch := simp [γ, circleMap_ne_center hs.ne'])
  have hnw θ : ‖γ θ‖ = s := by simp [γ, abs_of_pos hs]
  have hcont {x} (hx : x ∈ ball a s) :=
    hc.smul (hf.continuousOn.comp_continuous (by fun_prop) fun θ ↦ (hm hx (hnw θ).le).1)
  have hba := ball_mem_nhds a hs
  have hint := (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x θ ↦ c θ • fderiv ℂ f (x + γ θ • v)) (bound := fun _ ↦ s⁻¹ * (2 / s)) hba
    (mem_of_superset hba fun _ hx ↦ (hcont hx).aestronglyMeasurable)
    ((hcont (mem_ball_self hs)).intervalIntegrable 0 (2 * π))
    (hc.measurable.smul ((measurable_fderiv ℂ f).comp (by fun_prop))).aestronglyMeasurable
    (ae_of_all _ fun θ _ x hx ↦ by
      have hs' := hsub hx (hnw θ).le
      rw [norm_smul]
      gcongr
      · simp [c, hnw]
      · exact norm_fderiv_le_div_of_mapsTo_ball (hf.mono fun _ h ↦ (hU1 (hs' h)).1)
          (fun z hz ↦ (dist_triangle_right _ _ (f a)).trans (by
            linarith [mem_ball.1 (hU1 (hs' hz)).2, mem_ball.1 (hm hx (hnw θ).le).2])) hs)
    (intervalIntegrable_const (μ := volume))
    (ae_of_all _ fun θ _ x hx ↦
      (((hf.differentiableAt (hU.mem_nhds (hm hx (hnw θ).le).1)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const _)).const_smul (c θ)))).const_smul (2 * π * I : ℂ)⁻¹
  refine (hint.congr_of_eventuallyEq (mem_of_superset hba fun x hx ↦ ?_)).differentiableAt.differentiableWithinAt
  have h1 := (hf.fun_comp (by fun_prop) fun _ hζ ↦
    (hm hx (mem_closedBall_zero_iff.1 hζ)).1).deriv_eq_smul_circleIntegral hs
  have hfx := ((hf.differentiableAt (hU.mem_nhds (hm hx (by simp [hs.le])).1)).hasFDerivAt.comp_hasDerivAt
    0 (((hasDerivAt_id' 0).smul_const v).const_add x)).deriv
  simp [Function.comp_def] at hfx
  refine (eq_inv_smul_iff₀ (by simp [pi_ne_zero])).2 ?_
  rw [← hfx, ← h1]
  simp only [circleIntegral, deriv_circleMap, sub_zero, smul_smul, c, γ]
  congr 1; funext θ; congr 1
  field_simp [circleMap_ne_center hs.ne']

/-- Holomorphic inverse function theorem between finite-dimensional complex normed spaces of equal
dimension. -/
private lemma exists_local_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {Φ : E → F} {U : Set E} {b : E} {L : E →L[ℂ] F} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U)
    (hb : b ∈ U) (hL : HasFDerivAt Φ L b) (hker : ∀ u, L u = 0 → u = 0) :
    ∃ W ψ, IsOpen W ∧ Φ b ∈ W ∧ ψ (Φ b) = b ∧ DifferentiableOn ℂ ψ W ∧
      (∀ w ∈ W, ψ w ∈ U ∧ Φ (ψ w) = w) ∧ ∀ v, fderiv ℂ ψ (Φ b) (L v) = v := by
  have hΦc := (contDiffOn_succ_of_fderiv_apply (n := 0) hΦ (by simp) fun v ↦ contDiffOn_zero.2 <|
    (differentiableOn_fderiv_apply hU hΦ v).continuousOn.congr fun x hx ↦ by
      rw [fderivWithin_of_isOpen hU hx]).contDiffAt (hU.mem_nhds hb)
  have hinj := (injective_iff_map_eq_zero L).2 hker
  let M : E ≃L[ℂ] F := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩).toContinuousLinearEquiv
  have hs := hΦc.hasStrictFDerivAt (f' := M) hL one_ne_zero
  let H := hs.toOpenPartialHomeomorph Φ
  let ψ := hs.localInverse Φ M b
  obtain ⟨O, hO, hOo, hbO⟩ := _root_.eventually_nhds_iff.1
    ((hΦc.to_localInverse (f' := M) hL one_ne_zero).eventually (by simp))
  refine ⟨H.target ∩ ψ ⁻¹' U ∩ O, ψ, (H.isOpen_inter_preimage_symm hU).inter hOo,
    ⟨⟨hs.image_mem_toOpenPartialHomeomorph_target, by simp [ψ, hb]⟩, hbO⟩,
    hs.localInverse_apply_image,
    fun w hw ↦ ((hO w hw.2).differentiableAt one_ne_zero).differentiableWithinAt,
    fun w hw ↦ ⟨hw.1.2, H.right_inv hw.1.1⟩,
    fun v ↦ hs.to_localInverse.hasFDerivAt.fderiv.symm ▸ M.symm_apply_apply v⟩

/-- If `G, H` are holomorphic on an open `U ⊆ ℂ × ℂ` with `G = 0 → H = 0`, `G (0, 0) = 0`, and
`t ↦ H (0, t)` has finite vanishing order `≤ n` at `0`, then the zero set of `G` contains a
holomorphic graph over a small disk. -/
private lemma exists_zero_curve : ∀ (n : ℕ) {U : Set (ℂ × ℂ)} {G H : ℂ × ℂ → ℂ},
    IsOpen U → DifferentiableOn ℂ G U → DifferentiableOn ℂ H U →
    (∀ q ∈ U, G q = 0 → H q = 0) → (0, 0) ∈ U → G (0, 0) = 0 →
    analyticOrderAt (fun t ↦ H (0, t)) 0 ≤ n →
    ∃ s₁ δ γ, 0 < δ ∧ DifferentiableOn ℂ γ (ball s₁ δ) ∧
      ∀ s ∈ ball s₁ δ, γ s ∈ U ∧ G (γ s) = 0 ∧ (γ s).1 = s := by
  intro n U G H hU hG hH hGH hp hGp ho
  have hUo := (hU.preimage (f := Prod.mk 0) (by fun_prop)).mem_nhds hp
  have hAn := (hH.comp (f := Prod.mk 0) (by fun_prop) fun _ h ↦ h).analyticAt hUo
  cases n with
  | zero =>
    exact False.elim ((analyticOrderAt_eq_zero.1 (nonpos_iff_eq_zero.1 ho)).elim (· hAn) (· (hGH _ hp hGp)))
  | succ n =>
    by_cases h1 : ∀ q ∈ U, G q = 0 → fderiv ℂ H q (0, 1) = 0
    · refine exists_zero_curve n hU hG (differentiableOn_fderiv_apply hU hH (0, 1)) h1 hp hGp ?_
      have hadd := hAn.analyticOrderAt_deriv_add_one
      simp only [Function.comp_apply, hGH _ hp hGp, sub_zero] at hadd
      rw [analyticOrderAt_congr (mem_of_superset hUo fun t ht ↦
        ((hH.differentiableAt (hU.mem_nhds ht)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_const t (0 : ℂ)).prodMk (hasDerivAt_id' t))).deriv)] at hadd
      simpa using hadd.trans_le ho
    · push Not at h1
      obtain ⟨q, hq, hGq, hH'q⟩ := h1
      obtain ⟨W, ψ, hWo, hΦW, hψq, hψd, hψU, _⟩ := exists_local_inverse rfl hU
        (differentiableOn_fst.prodMk hH) hq
        (hasFDerivAt_fst.prodMk (hH.differentiableAt (hU.mem_nhds hq)).hasFDerivAt)
        fun ⟨u₁, u₂⟩ hu ↦ by
          simp [Prod.ext_iff] at hu
          rcases hu with ⟨rfl, h2⟩
          rw [show (0, u₂) = u₂ • ((0 : ℂ), (1 : ℂ)) by simp, map_smul, smul_eq_mul] at h2
          simp [(mul_eq_zero.1 h2).resolve_right hH'q]
      rw [hGH q hq hGq] at hΦW hψq
      obtain ⟨r₀, hr₀, hr₀W⟩ := nhds_basis_closedBall.mem_iff.1 (hWo.mem_nhds hΦW)
      rw [← closedBall_prod_same] at hr₀W
      have hB := ball_mem_nhds q.1 hr₀
      have hp0 {s} (hs : s ∈ ball q.1 r₀) :=
        hr₀W (mk_mem_prod (ball_subset_closedBall hs) (mem_closedBall_self hr₀.le))
      let g : ℂ × ℂ → ℂ := G ∘ ψ
      have hGt0 {s w} (hm : (s, w) ∈ W) (h0 : g (s, w) = 0) : w = 0 :=
        (Prod.mk.inj (hψU _ hm).2).2.symm.trans (hGH _ (hψU _ hm).1 h0)
      have hGd : DifferentiableOn ℂ g W := hG.comp hψd fun _ h ↦ (hψU _ h).1
      have hGt_an : AnalyticAt ℂ (fun s ↦ g (s, 0)) q.1 := (hGd.comp (by fun_prop) fun _ ↦ hp0).analyticAt hB
      rcases hGt_an.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
      · obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1 (inter_mem hB hzero)
        exact ⟨q.1, δ, fun s ↦ ψ (s, 0), hδ, hψd.comp (by fun_prop) fun _ hs ↦ hp0 (hδB hs).1,
          fun s hs ↦ let h := hψU _ (hp0 (hδB hs).1); ⟨h.1, (hδB hs).2, congrArg Prod.fst h.2⟩⟩
      · let Jf : ℂ → ℂ := fun s ↦ ∮ w in C(0, r₀), (w - 0)⁻¹ • (g (s, w))⁻¹
        have hI_at : ContinuousAt Jf q.1 := (continuousOn_iff_continuous_domRestrict.2 (by
          apply continuous_parametric_intervalIntegral_of_continuous'
          have hm (x : ball q.1 r₀ × ℝ) :=
            hr₀W (mk_mem_prod (ball_subset_closedBall x.1.2) (circleMap_mem_closedBall 0 hr₀.le x.2))
          dsimp only [uncurry_def]
          simp only [deriv_circleMap, sub_zero, smul_eq_mul, mul_comm _ I, mul_assoc,
            mul_inv_cancel_left₀ (circleMap_ne_center hr₀.ne')]
          exact continuous_const.mul ((hGd.continuousOn.comp_continuous (by fun_prop) hm).inv₀
            fun x h0 ↦ circleMap_ne_center hr₀.ne' (hGt0 (hm x) h0)))).continuousAt hB
        have h0eq : (0 : ℂ) = 2 * π * I := tendsto_nhds_unique
          (by simpa [g, hψq, hGq] using (hGt_an.continuousAt.fun_mul hI_at).mono_left nhdsWithin_le_nhds)
          (tendsto_const_nhds.congr' ((Eventually.and (nhdsWithin_le_nhds hB) hne).mono fun s ⟨hs, hne0⟩ ↦ by
            have hc := DifferentiableOn.circleIntegral_sub_inv_smul
              ((hGd.comp (f := Prod.mk s) (by fun_prop) fun w hw ↦
                hr₀W ⟨ball_subset_closedBall hs, hw⟩).inv
                fun w hw h0 ↦ hne0 (by rwa [hGt0 (hr₀W ⟨ball_subset_closedBall hs, hw⟩) h0] at h0))
              (mem_ball_self hr₀)
            rw [show Jf s = _ from hc, smul_eq_mul, mul_left_comm]
            simpa [g] using mul_inv_cancel₀ hne0))
        exact False.elim ((by simp [pi_ne_zero] : (0 : ℂ) ≠ 2 * π * I) h0eq)

end InjectiveHolomorphicJacobianNeZero

/-- Bochner–Martin / Osgood theorem: an injective holomorphic map on an open subset of `ℂᵏ` has
nonvanishing Jacobian determinant everywhere. -/
theorem InjectiveHolomorphicJacobianNeZero.proof : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k with
  | zero =>
    intro U f _ _ _ x _ hdet
    rw [LinearMap.det_eq_one_of_subsingleton] at hdet
    exact one_ne_zero hdet
  | succ k ih =>
    cases k with
    | zero => exact fun _ _ hU hf hinj _ hx ↦ InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx
    | succ k =>
      intro U f hU hf hinj a ha hdet
      let J z := LinearMap.det (fderiv ℂ f z : (Fin (k + 2) → ℂ) →ₗ[ℂ] Fin (k + 2) → ℂ)
      let pr (m : Fin (k + 2)) : (Fin (k + 2) → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj m
      by_cases hflat : ∀ b ∈ U, J b = 0 → fderiv ℂ f b = 0
      · have hJ : DifferentiableOn ℂ J U :=
          (DifferentiableOn.fun_sum (u := univ) fun (σ : Equiv.Perm (Fin (k + 2))) _ w hw ↦
            ((HasFDerivWithinAt.finsetProd (u := univ) fun i _ ↦
              ((pr (σ i)).differentiable.comp_differentiableOn
                (InjectiveHolomorphicJacobianNeZero.differentiableOn_fderiv_apply hU hf (single i 1))
                w hw).hasFDerivWithinAt).const_smul
              (Equiv.Perm.sign σ)).differentiableWithinAt).congr fun w _ ↦ by
            dsimp [J]; rw [← LinearMap.det_toMatrix', Matrix.det_apply]; rfl
        obtain ⟨R, hR, hball⟩ := isOpen_iff.1 hU a ha
        by_cases hall : ∀ z ∈ ball a R, J z = 0
        · obtain ⟨y, hy, hne⟩ :=
            InjectiveHolomorphicJacobianNeZero.exists_mem_ne_of_mem_nhds (ball_mem_nhds a hR)
          exact hne (hinj (hball hy) ha ((convex_ball a R).is_const_of_fderivWithin_eq_zero (hf.mono hball)
            (fun w hw ↦ (fderivWithin_of_isOpen isOpen_ball hw).trans (hflat w (hball hw) (hall w hw)))
            hy (mem_ball_self hR)))
        push Not at hall
        obtain ⟨z₀, hz₀B, hz₀⟩ := hall
        let v := z₀ - a
        have hv0 : v ≠ 0 := sub_ne_zero.2 fun h ↦ hz₀ (h ▸ hdet)
        obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hv0
        let aff (p : ℂ × ℂ) := a + p.1 • single (j₀.succAbove 0) 1 + p.2 • v
        have haffd : Differentiable ℂ aff := by fun_prop
        have haff_inj : Injective aff := fun ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq ↦ by
          have h1 := congrFun hpq j₀; have h0 := congrFun hpq (j₀.succAbove 0)
          simp [aff, (Fin.succAbove_ne j₀ 0).symm] at h1 h0
          obtain rfl := h1.resolve_right hj₀
          exact Prod.ext (by simpa using h0) rfl
        have hG : DifferentiableOn ℂ (J ∘ aff) (aff ⁻¹' ball a R) :=
          hJ.comp haffd.differentiableOn fun _ h ↦ hball h
        have hv_pos := norm_pos_iff.2 hv0
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 fun htop ↦ hz₀ (by
          simpa [aff, v] using ((hG.comp (f := Prod.mk 0) (s := ball 0 (R / ‖v‖)) (by fun_prop)
            fun t ht ↦ by
              show aff (0, t) ∈ ball a R
              simpa [aff, mem_ball, dist_eq_norm, norm_smul, lt_div_iff₀ hv_pos] using ht).analyticOnNhd
            isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
            (convex_ball _ _).isPreconnected (mem_ball_self (by positivity))
            (analyticOrderAt_eq_top.1 htop)
            (x := 1) (by simpa [v, mem_ball, dist_eq_norm, one_lt_div hv_pos] using hz₀B))
        obtain ⟨s₀, δ, γ, hδ, hγd, hγ⟩ :=
          InjectiveHolomorphicJacobianNeZero.exists_zero_curve n
            (isOpen_ball.preimage haffd.continuous) hG hG (fun _ _ h ↦ h)
            (by simpa [aff] using hR) (by simpa [aff] using hdet) hn.ge
        obtain ⟨s₁, hs₁, hne⟩ :=
          InjectiveHolomorphicJacobianNeZero.exists_mem_ne_of_mem_nhds (ball_mem_nhds s₀ hδ)
        have hs₀ : s₀ ∈ ball s₀ δ := mem_ball_self hδ
        have hUγ {s} (hs : s ∈ ball s₀ δ) := hball (hγ _ hs).1
        refine hne ?_
        simpa [(hγ s₁ hs₁).2.2, (hγ s₀ hs₀).2.2] using congrArg Prod.fst (haff_inj (hinj
          (hUγ hs₁) (hUγ hs₀) ((convex_ball s₀ δ).is_const_of_fderivWithin_eq_zero (f := f ∘ aff ∘ γ)
            (hf.comp (haffd.comp_differentiableOn hγd) fun _ hs ↦ hUγ hs)
            (fun s hs ↦ by
              rw [fderivWithin_of_isOpen isOpen_ball hs,
                (((hf.differentiableAt (hU.mem_nhds (hUγ hs))).hasFDerivAt.comp s
                  ((haffd _).hasFDerivAt.comp s
                    (hγd.differentiableAt (isOpen_ball.mem_nhds hs)).hasFDerivAt))).fderiv,
                hflat _ (hUγ hs) (hγ s hs).2.1, ContinuousLinearMap.zero_comp]) hs₁ hs₀)))
      · push Not at hflat
        obtain ⟨b, hb, hdb, hne⟩ := hflat
        obtain ⟨i, j, hij⟩ : ∃ i j : Fin (k + 2), fderiv ℂ f b (single j 1) i ≠ 0 := by
          by_contra! h
          exact hne (ContinuousLinearMap.coe_injective
            ((Pi.basisFun ℂ (Fin (k + 2))).ext fun c ↦ funext fun i ↦ by simpa using h i c))
        let rm (m : Fin (k + 2)) := ContinuousLinearMap.pi fun r ↦ pr (m.succAbove r)
        obtain ⟨W, ψ, hWo, hΦW, hψb, hψd, hψU, hψder⟩ :=
          InjectiveHolomorphicJacobianNeZero.exists_local_inverse
            (by simp [Module.finrank_prod]; lia) (Φ := fun z ↦ (f z i, rm j z)) hU
            (((pr i).differentiable.comp_differentiableOn hf).prodMk
              (rm j).differentiable.differentiableOn) hb
            (((pr i).hasFDerivAt.comp b
              (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt).prodMk (rm j).hasFDerivAt)
            fun u hu ↦ by
              obtain ⟨h1, h2⟩ := Prod.mk_eq_zero.1 hu
              have hsub : u = u j • single j 1 :=
                funext (j.forall_iff_succAbove.2 ⟨by simp, fun r ↦ by simpa [rm, pr] using congrFun h2 r⟩)
              rw [hsub, map_smul, smul_eq_mul] at h1
              rw [hsub, (mul_eq_zero.1 h1).resolve_right hij, zero_smul]
        let u₀ := rm j b
        let g u := rm i (f (ψ (f b i, u)))
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
          (LinearMap.det_eq_zero_iff_ker_ne_bot.1 hdb)
        change fderiv ℂ f b v = 0 at hv
        have hψv : fderiv ℂ ψ (f b i, rm j b) (0, rm j v) = v := by simpa [hv] using hψder v
        have hgw : HasFDerivAt g _ u₀ :=
          (rm i).hasFDerivAt.comp u₀ ((hψb.symm ▸
            (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt).comp u₀
            ((hψd.differentiableAt (hWo.mem_nhds hΦW)).hasFDerivAt.comp u₀
              ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _))))
        exact ih (Prod.mk (f b i) ⁻¹' W) g (hWo.preimage (by fun_prop))
          ((rm i).differentiable.comp_differentiableOn
            (hf.comp (hψd.comp (by fun_prop) fun _ h ↦ h) fun _ h ↦ (hψU _ h).1))
          (fun u₁ hu₁ u₂ hu₂ heq ↦ by
            obtain ⟨h1a, h1b⟩ := Prod.mk.inj (hψU _ hu₁).2
            obtain ⟨h2a, h2b⟩ := Prod.mk.inj (hψU _ hu₂).2
            have h12 := hinj (hψU _ hu₁).1 (hψU _ hu₂).1 (funext (i.forall_iff_succAbove.2
              ⟨h1a.trans h2a.symm, fun r ↦ by simpa [g, rm, pr] using congrFun heq r⟩))
            exact h1b.symm.trans (h12 ▸ h2b))
          u₀ hΦW (LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2
            ⟨rm j v, by simp [hgw.fderiv, hψb, hψv, hv], fun h0 ↦ hv0 (by
              rw [← hψv, h0]; exact map_zero _)⟩))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
