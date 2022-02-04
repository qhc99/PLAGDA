

data 𝔹 : Set where
    tt : 𝔹
    ff : 𝔹

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then t else f = t
if ff then t else f = f