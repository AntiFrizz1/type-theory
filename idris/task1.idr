%default total

moreThan : (a : Nat) -> (b : Nat) -> Type
moreThan a b = (k : Nat ** a = b + (S k))

step1 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (a = b + (S k)) -> (a * a = (b + (S k)) * (b + (S k)))
step1 a b k prf = rewrite prf in Refl

step2 : (b : Nat) -> (k : Nat) -> (b + (S k)) * (b + (S k)) = b * (b + (S k)) + (S k) * (b + (S k))
step2 b k = multDistributesOverPlusLeft b (S k) (b + (S k))

step3 : (b : Nat) -> (k : Nat) -> (b + (S k)) * (b + (S k)) = (b * b + b * (S k)) + (S k) * (b + (S k))
step3 b k = rewrite sym (multDistributesOverPlusRight b b (S k)) in step2 b k

step4 : (b : Nat) -> (k : Nat) -> (b + (S k)) * (b + (S k)) = b * b + (b * (S k) + (S k) * (b + (S k)))
step4 b k = rewrite (plusAssociative (b * b) (b * (S k)) ((S k) * (b + (S k)))) in (step3 b k)

step5 : (b : Nat) -> (k:Nat) -> b * (S k) + (S k) * (b + (S k)) = b * (S k) + (b + (S k)) + k * (b + (S k))
step5 b k = rewrite plusAssociative (b * (S k)) (b + (S k)) (k * (b + (S k))) in Refl

step6 : (b: Nat) -> (k : Nat) -> b * (S k) + (S k) * (b + (S k)) = (b * (S k) + S (b + k)) + k * (b + (S k))
step6 b k = rewrite ((plusSuccRightSucc b k)) in (step5 b k)

step7 : (b: Nat) -> (k : Nat) -> b * (S k) + (S k) * (b + (S k)) = b * (S k) + (S (b + k) + k * (b + (S k)))
step7 b k = rewrite (plusAssociative (b * (S k)) (S (b + k)) (k * (b + (S k)))) in (step6 b k)

step8 : (b: Nat) -> (k : Nat) -> b * (S k) + (S k) * (b + (S k)) = b * (S k) + (k * (b + (S k)) + S (b + k))
step8 b k = rewrite sym (plusCommutative (S (b + k)) (k * (b + (S k)))) in (step7 b k)

step9 : (b: Nat) -> (k : Nat) -> b * (S k) + (S k) * (b + (S k)) = (b * (S k) + k * (b + (S k))) + S (b + k)
step9 b k = rewrite sym (plusAssociative (b * (S k)) (k * (b + (S k))) (S (b + k))) in (step8 b k)

step10 : (b: Nat) -> (k : Nat) -> b * (S k) + (S k) * (b + (S k)) = S ((b * (S k) + k * (b + (S k))) + (b + k))
step10 b k = rewrite (plusSuccRightSucc ((b * (S k) + k * (b + (S k)))) (b + k)) in (step9 b k)

step11 : (b: Nat) -> (k : Nat) -> b * (S k) + (S k) * (b + (S k)) = S (b * (S k) + (k * (b + (S k)) + (b + k)))
step11 b k = rewrite plusAssociative (b * (S k)) (k * (b + (S k))) (b + k) in (step10 b k)

step12 : (b : Nat) -> (k : Nat) -> (b + (S k)) * (b + (S k)) = b * b + S (b * (S k) + (k * (b + (S k)) + (b + k)))
step12 b k = rewrite sym (step11 b k) in (step4 b k)

step13 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (a = b + (S k)) -> (a * a = b * b + S (b * (S k) + (k * (b + (S k)) + (b + k))))
step13 a b k prf = rewrite sym (step12 b k) in (step1 a b k prf)

task : {a : Nat} ->  {b : Nat} -> moreThan a b -> moreThan (a * a) (b * b)
task {a} {b} (k ** prf) = ((b * (S k) + (k * (b + (S k)) + (b + k))) ** (step13 a b k prf))
