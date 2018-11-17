--import tactic.finish
-- This is an example as per the instructions 
-- in the introduction. The follwing means: let 
-- there be an example such that P, Q, and R are 
-- Prop(ositions), where there is a hypothesis HP
-- that refers to the proposition P, and there is
-- a hypothesis HQ that refers to the proposition 
-- Q, and P is the variable to find the truth value
-- of. As such, we begin the proof, give a valid
-- proof of HP, which means that P has a truth value.
-- Then end not being underlined in red or green 
-- shows that the proof is a valid one to be able to
-- arrive at the conclusion that P is defined. 
example (P Q R : Prop) (HP : P) (HQ : Q) : P :=
begin
  exact HP,
end

-- proof of P → Q, and then proving P, to prove Q 
theorem easy (P Q : Prop) (HP :P) (HPQ : P → Q) : Q :=
begin
  exact HPQ HP,
end

-- proving P → q is the idea that we should assume we 
-- already have a proof of P, and then somehow deduce
-- a proof of Q. This can be done in Lean by the
-- intro tactic.

theorem Q_implies_P_impliesQ (P Q : Prop) (HQ : Q) : P → Q :=
-- propositions p and q given such that hq is a proof of q, 
-- and hence define p → q.
begin
  intro HP, 
  exact HQ,
end

-- the intro tactic is a cons for p → q
-- if the goal is p → q then we can type intro hp and then lean proves our goal, modulo some other simpler things (proof of q)

theorem P_implies_P (P : Prop) : P → P :=
begin
  intro HP,
  exact HP,
end

example (P Q : Prop) : P ∧ (P → Q) → Q :=
begin
    intro HPnPQ,
    cases HPnPQ with HP HPQ,
    exact HPQ HP,
end

theorem and_comm1 (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
    assume HPQ : P ∧ Q,
    have HP : P, from and.left HPQ,
    have HQ : Q, from and.right HPQ,
    show Q ∧ P, from and.intro HQ HP, 
end

constant m : nat 
constant n : nat
constants b1 b2 : bool

#check m
#check n 
#check n + 0
#check m * (n + 0) 
#check b1
#check b1 && b2
#check b1 || b2 
#check tt

/-Text inbetween these symbols is ignored.
aka. Mass commentating tool!!-/




-- theorem comm_1 (A B C : Prop) : (A ∧ B) ∧ C ↔ A ∧ (B ∧ C) :=
-- begin
--     split,
--     {
--         intro HAnBnC,
--         cases HAnBnC with HAnB HC,
--         cases HAnB with HA HB,
--         split,
--         {
--             exact HA,

--         },
--         {
--             split,
--             {
--                 exact HB,
--             },
--             {
--                 exact HC,
--             },
--         },

--     },
    
-- end

theorem needs_intros (P Q R :Prop) (HR : R) : P → (Q → R) :=
begin 
    intro HP, 
    intro HQ,
    exact HR,
end

theorem very_easy : true :=
begin 
    exact trivial,
end

theorem very_hard: false := 
begin
    sorry,
end

theorem false_implies_false : false → false :=
begin 
    intro Hfalse,
    exact Hfalse,
end

theorem not_not (P : Prop) : P → ¬ (¬ P) :=
begin
    intro HP,
    intro HnP,
    apply HnP, -- to reduce goal from false to P. 
    exact HP,
end

theorem contrapos (P Q : Prop) (HPQ : P → Q) : ¬ Q → ¬ P :=
begin
    intro HnQ,
    intro HP,
    apply HnQ,
    apply HPQ,
    apply HP,
end

theorem P_implies_P_or_Q (P Q :Prop) (HP : P) : P ∨ Q :=
begin
    left,
    exact HP,
end

theorem Q_implies_P_or_Q (P Q : Prop) (HQ : Q) : P ∨ Q :=
begin 
    right,
    exact HQ,
end

theorem dont_get_lost (P Q : Prop) (HQ : Q) : P ∨ Q :=
begin
    left,
        -- goal no longer provable; as there is nothing left to deduce to be able to prove P.
    sorry,
end

theorem or_symmetry (P Q :Prop) : P ∨ Q → Q ∨ P :=
begin
    intro HPQ,
    cases HPQ with HP HQ,
    {
        right,
        exact HP,
    },
    {
        left,
        exact HQ,
    },
end

theorem or_experiment (P Q R :Prop) (HPQR : P ∨ Q ∨ R) : true :=
begin
    cases HPQR with HP HQR,
    sorry,
    sorry,
end

theorem or_associativity (P Q R : Prop) : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
begin 
    intro HPQR,
    cases HPQR with HP HQR,
    {
        left,
        left,
        exact HP,
    },
    {
        cases HQR with HQ HR,
        {
            left,
            right,
            exact HQ,
        },
        {
            right,
            exact HR,
        },
    },
end

theorem and_definition (P Q : Prop) (HP : P) (HQ : Q) : P ∧ Q :=
begin
    split,
    {exact HP,},
    {exact HQ,},
end

theorem and_symmetry (P Q : Prop) (HP :P) (HQ : Q) : P ∧ Q → Q ∧ P :=
begin
    intro HPQ,
    split,
    cases HPQ with HP HQ,
    {exact HQ,},
    {exact HP,},
end

theorem and_transitivity (P Q R : Prop) : (P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) :=
begin
    intro HPQR,
    cases HPQR with HPQ HQR,
    split,
        cases HPQ with HP HQ,
        exact HP,
        cases HQR with HQ HR,
        exact HR, 
end

theorem iff_symmetric (P Q : Prop) : (P ↔ Q) ↔ (Q ↔ P) :=
begin
    split,
    intro HPiffQ,
    cases HPiffQ with HPtoQ HQtoP,
    split,
        exact HQtoP,
        exact HPtoQ,
    
    intro HQiffP,
    cases HQiffP with HQtoP HPtoQ,
    split,
        exact HPtoQ,
        exact HQtoP,
end

theorem iff_transitive (P Q R : Prop) : (P ↔ Q) ∧ (Q ↔ R) → (P ↔ R) :=
begin
    intro H,
    cases H with HPiffQ HQiffR,
    rw HPiffQ,
    exact HQiffR,
end

theorem not_not_1 (P : Prop) : ¬ (¬ P) → P :=
begin
    cases (classical.em P) with HP HnP,
    {
        intro HnnP,
        exact HP,
    },
    {
        intro HnnP,
        exfalso,
        apply HnnP,
        exact HnP,
    }, 
end

theorem contra (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
begin
    intro HnQnP,
    intro HP,

    cases (classical.em Q) with HQ HnQ,
    {
        exact HQ,
    },
    {
        exfalso,
        apply HnQnP,
        exact HnQ,
        exact HP,
    },
end

theorem name1 (A B : Prop) : (¬ (A ∧ B)) ↔ (¬ A ∨ ¬ B) :=
begin
    cases classical.em A with HA HnA,
    {
        cases classical.em B with HB HnB,
        {
            have HAB := and_definition A B HA HB,
            split,
            {
                intro H,
                exfalso,
                exact H HAB,
            },
            {
                intro H,
                cases H with H1 H2,
                {
                    exfalso,
                    contradiction,
                },
                {
                    exfalso,
                    contradiction,
                }
            }
        },
        {
            split,
            {
                intro H,
                right,
                exact HnB,
            },
            {
                intro H,
                cases H with H1 H2,
                {
                    exfalso,
                    exact H1 HA,
                },
                {
                    intro HAB,
                    cases HAB with _ HB,
                    exact HnB HB,
                },
            },
        },
    },
    {
        cases classical.em B with HB HnB,
        {
            split,
            intro _,
            left,
            exact HnA,
            intro _,
            intro H,
            cases H with HA _,
            exact HnA HA,
        },
        {
            split,
            intro _,
            left,
            exact HnA,
            intro _,
            intro H,
            cases H with HA _,
            exact HnA HA,
        }
    }
    -- intro HnAaB,
    -- right,
    -- intro HB,
    -- apply HnAaB,
    -- split,
    -- sorry,
    -- sorry,

    -- intro HnAnB,
    -- cases HnAnB with HnA HnB,
    --     {
    --         intro HAaB,
    --         sorry,
    --     }
    -- sorry,

end

theorem name2 (P Q : Prop) (HP : P) (HQ : Q) : P ∧ Q :=
begin
    split,
    exact HP,
    exact HQ,
end

