module RusselsForest

import Data.DPair
import Decidable.Decidable
import Data.Fun
import Data.Rel
import ToMockAMockingbird
import BirdsGalore
import AGalleryOfSageBirds

%default total 

parameters {auto b : Type} {auto _ : Bird b} (a : b) (Sings : b -> Type) 
    0 Law1 : Type
    Law1 = (x : b) -> ((Sings $ a <*> x) -> Sings $ x <*> x, (Sings $ x <*> x) -> Sings $ a <*> x)

    0 Law2 : Type 
    Law2 = (x : b) -> Exists(\x' => (y : b) -> ((Sings $ x' <*> y) -> Not(Sings $ x <*> y), Not(Sings $ x' <*> y) -> Sings $ x' <*> y))

    0 question1 : Decidable 1 [b] Sings => Law1 -> Law2 -> Void 
    question1 law1 law2 = 
        let Evidence a' prf = law2 a
            (prf1,prf2) = prf a'
            (prf3, prf4) = law1 a'
        in case decision [b] Sings (a' <*> a') of 
            (Yes prf5) => prf1 prf5 $ prf4 prf5
            (No contra) => contra $ prf2 contra
    
    0 Law3 : Type 
    Law3 = Exists(\xN => (x : b) -> ((Sings $ xN <*> x) -> Not(Sings x), Not(Sings $ xN <*> x) -> (Sings x)))

    0 question2 : Decidable 1 [b] Sings => Law3 -> {xS : b} -> SageBird xS -> Void
    question2 (Evidence xN prf) sage = 
        let eq1 = sage xN
            (prf1, prf2) = prf (xS <*> xN)
        in case decision [b] Sings (xN <*> (xS <*> xN)) of 
            (Yes prf3) => prf1 prf3 $ rewrite eq1 in prf3
            (No contra) => contra $ rewrite sym eq1 in prf2 contra
    
    0 Law4 : Type 
    Law4 = Exists(\xA => (x : b) -> (y : b) -> ((Sings $ xA <*> x <*> y) -> (Not(Sings x), Not(Sings y)), Not(Sings $ xA <*> x <*> y) -> Either (Sings x) (Sings y) ))

    0 question3 : Law4 -> {xS : b} -> SageBird xS -> Void
    question3 (Evidence xA prf) sage = 
        let prf1 = lemma1 xA
            prf2 = lemma2 ((xA <*> xA) <*> (xS <*> (xA <*> xA)))
        in prf1 prf2
    where 
        lemma1 : (x : b) -> Not(Sings ((xA <*> x) <*> (xS <*> (xA <*> x))))
        lemma1 x prf' = 
            let eq1 = sage (xA <*> x)
                (prf1, prf2) = prf x (xS <*> (xA <*> x))
                (prf1', prf2') = prf1 prf'
            in prf2' $ rewrite eq1 in prf'
        lemma2 : (x : b) -> Sings x
        lemma2 x = 
            let prf2 = lemma1 x
                eq1 = sage (xA <*> x)
                (prf3, prf4) = prf x  (xS <*> (xA <*> x))
            in case prf4 prf2 of 
                (Left x) => x 
                (Right x) => void $ prf2 $ rewrite sym eq1 in x 

        
    
