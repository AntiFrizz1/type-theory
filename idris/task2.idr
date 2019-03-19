%default total

maxMinAZ : (a: Nat) -> maximum a (minimum a Z) = a
maxMinAZ Z = Refl
maxMinAZ (S a) = Refl

maxMinBZ : (b : Nat) -> maximum Z (minimum Z b) = Z
maxMinBZ Z = Refl
maxMinBZ (S a) = Refl

task : (a : Nat) -> (b : Nat) -> maximum a (minimum a b) = a
task a Z = maxMinAZ a
task Z b = maxMinBZ b
task (S a) (S b) = rewrite task a b in Refl
