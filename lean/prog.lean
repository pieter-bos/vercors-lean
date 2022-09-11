inductive V
| int : ℤ → V
| bool : bool → V

inductive E
| const : V → E
| var : string → E
| add : E → E → E
| less : E → E → E

inductive P
| skip : P
| seq : P → P → P
| assign : string → E → P
| select : E → P → P → P
| while : E → P → P

def stat := string → option V

def emp : stat := λ_, option.none

def stat.get (σ : stat) (var : string) (v : V) : Prop :=
match σ var with
| option.none := false
| option.some v' := v = v'
end

inductive eval : stat → E → V → Prop
| const : ∀σ v, 
    eval σ (E.const v) v
| var : ∀σ var v, 
    stat.get σ var v → eval σ (E.var var) v
| add : ∀σ e e' z z',
    eval σ e (V.int z) → eval σ e' (V.int z') → eval σ (E.add e e') (V.int (z + z'))
| less : ∀σ e e' z z',
    eval σ e (V.int z) → eval σ e' (V.int z') → eval σ (E.less e e') (V.bool (z < z'))

inductive small_step : (P × stat) → (P × stat) → Prop
| seq_emp : ∀s p, 
    small_step (P.seq P.skip p, s) (p, s)
| seq_progress : ∀s s' p p' q,
    small_step (p, s) (p', s') →
      small_step (P.seq p q, s) (P.seq p' q, s')
| assign : ∀σ var v e,
    eval σ e v → 
      small_step (P.assign var e, σ) (P.skip, λvar', if var = var' then v else σ var')
| select_false : ∀σ cond p p',
    eval σ cond (V.bool ff) →
      small_step (P.select cond p p', σ) (p', σ)
| select_true : ∀σ cond p p',
    eval σ cond (V.bool tt) →
      small_step (P.select cond p p', σ) (p, σ)
| while : ∀σ cond p,
    small_step (P.while cond p, σ)
      (P.select cond (P.seq p (P.while cond p)) P.skip, σ)

inductive small_step_star : (P × stat) → (P × stat) → Prop
| skip : ∀σ, 
    small_step_star (P.skip, σ) (P.skip, σ)
| step : ∀p_s p_s' p_s'',
    small_step p_s p_s' →
    small_step_star p_s' p_s'' →
      small_step_star p_s p_s''

inductive big_step : P → stat → stat → Prop
| skip : ∀σ, 
    big_step P.skip σ σ
| seq : ∀σ σ' σ'' p p',
    big_step p σ σ' →
    big_step p' σ' σ'' →
      big_step (P.seq p p') σ σ''
| assign : ∀σ var e v,
    eval σ e v →
      big_step (P.assign var e) σ (λvar', if var = var' then v else σ var')
| select_false : ∀σ σ' cond p p',
    eval σ cond (V.bool ff) →
    big_step p' σ σ' →
      big_step (P.select cond p p') σ σ'
| select_true : ∀σ σ' cond p p',
    eval σ cond (V.bool tt) →
    big_step p σ σ' →
      big_step (P.select cond p p') σ σ'
| while_false : ∀σ cond p,
    eval σ cond (V.bool ff) →
      big_step (P.while cond p) σ σ
| while_true : ∀σ σ' σ'' cond p,
    eval σ cond (V.bool tt) →
    big_step p σ σ' →
    big_step (P.while cond p) σ' σ'' →
      big_step (P.while cond p) σ σ''

lemma star_step_right (ps ps' ps'' : P × stat) (h1 : small_step_star ps ps') (h2 : small_step ps' ps'')
: small_step_star ps ps'' := begin
  induction h1 generalizing ps'',
  case skip {
    -- absurd; we have small_step ps' ps''
    cases h2,
  },
  case step : hps hps' hps'' step star ih {
    sorry,
  },
end

lemma star_star (ps ps' ps'' : P × stat) (h1 : small_step_star ps ps') (h2 : small_step_star ps' ps'') 
: small_step_star ps ps'' := begin
  induction h2,
  case skip {
    exact h1,
  },
  case step : hps hps' hps'' head tail ih {
    apply ih,
    sorry,
  },
end

theorem small_step_injective (σ τ τ' : stat) (p p' : P) :
  small_step (p, σ) (p', τ) → small_step (p, σ) (p', τ') → τ = τ' := begin
  intros step step',
  induction step,
  repeat { sorry, },
end