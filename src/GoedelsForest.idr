module GoedelsForest

import Data.DPair
import Decidable.Decidable
import Data.Fun
import Data.Rel
import ToMockAMockingbird
import BirdsGalore
import AGalleryOfSageBirds

%default total 

parameters {auto b : Type} {auto _ : Bird b} (xN : b) (Sings : b -> Type) (IsNightingale : b -> Type) (mate : b -> b) (assosiate : b -> b)
    Condition1 : Type
    Condition1 = (x : b) -> (IsNightingale x) -> Sings x

    Condition2a : Type
    Condition2a = (x : b) -> (y : b) -> (Sings $ (mate x) <*> y) -> Not(Sings $ x <*> y)
    Condition2b : Type 
    Condition2b = (x : b) -> (y : b) -> Not(Sings $ x <*> y) -> (Sings $ (mate x) <*> y)

    Condition3a : Type
    Condition3a = (x : b) -> (y : b) -> (Sings $ (assosiate x) <*> y) -> Sings $ x <*> (y <*> y)
    Condition3b : Type
    Condition3b = (x : b) -> (y : b) -> (Sings $ x <*> (y <*> y)) -> (Sings $ (assosiate x) <*> y)

    Condition4a : Type 
    Condition4a = (x : b) -> (Sings $ xN <*> x) -> IsNightingale x
    Condition4b : Type 
    Condition4b = (x : b) -> (IsNightingale x) -> (Sings $ xN <*> x)

    0 question1 : 
        Condition1 ->
        Condition2a -> Condition2b ->
        Condition3a -> Condition3b ->
        Condition4a -> Condition4b -> 
        Exists(\x => (Sings x, Not(IsNightingale x)))
    question1 condition1 condition2a condition2b condition3a condition3b condition4a condition4b = 
        let (xA ** eq) = the (xA ** xA = (assosiate $ mate xN)) ((assosiate $ mate xN) ** Refl)
            prf1 = lemma1 eq xA
            prf2 = lemma2 eq xA
        in Evidence (xA<*>xA) 
            (prf2 $ \prf3 => prf1 (condition1 _ prf3) prf3, 
            \prf3 => prf1 (condition1 _ prf3) prf3)
    where 
        lemma1 : xA = (assosiate $ mate xN) -> (x : b) -> (Sings $ xA <*> x) -> Not(IsNightingale $ x <*> x)
        lemma1 eq x prf1 prf2 = 
            let prf3 = condition3a (mate xN) x $ rewrite sym eq in prf1
                prf4 = condition2a xN  (x <*> x) prf3
                prf5 = condition4b (x <*> x) prf2
            in prf4 prf5
        
        lemma2 : xA = (assosiate $ mate xN) -> (x : b) -> Not(IsNightingale $ x <*> x) -> (Sings $ xA <*> x)
        lemma2 eq x prf = 
            let prf2 = condition2b xN (x <*> x)
            in rewrite eq in condition3b (mate xN) x $ prf2 (\prf3 => prf $ condition4a _ prf3)

    0 question2 :  
        Condition1 ->
        Condition2a -> Condition2b ->
        Condition3a -> Condition3b ->
        Condition4a -> Condition4b -> 
        Exists(\x => (Sings x, Not(IsNightingale x)))
    question2 condition1 condition2a condition2b condition3a condition3b condition4a condition4b = 
        let (xA1 ** eq) = the (xA1 ** xA1 = (mate $ assosiate xN)) ((mate $ assosiate xN) ** Refl)
            prf1 = lemma1 eq xA1
            prf2 = lemma2 eq xA1
        in Evidence (xA1<*>xA1) 
            (prf2 $ \prf3 => prf1 (condition1 _ prf3) prf3, 
            \prf3 => prf1 (condition1 _ prf3) prf3)
    where 
        lemma1 : xA1 = (mate $ assosiate xN) -> (x : b) -> (Sings $ xA1 <*> x) -> Not(IsNightingale $ x <*> x)
        lemma1 eq x prf1 prf2 = 
            condition2a (assosiate xN) x (rewrite sym eq in prf1) $ condition3b _ _ $ condition4b _ prf2
        
        lemma2 : xA1 = (mate $ assosiate xN) -> (x : b) -> (Not $ IsNightingale $ x <*> x) -> (Sings $ xA1 <*> x)
        lemma2 eq x prf = 
            rewrite eq in condition2b  (assosiate xN) x $ 
                \prf2 => prf $ condition4a _ $ condition3a _ _ prf2
        

    0 question3a : Decidable 1 [b] Sings => (xA : b) -> 
        Condition3a -> Condition3b ->
        Either (Exists $ \x => (Sings $ xA <*> x, Sings x)) (Exists $ \x => (Not $ Sings $ xA <*> x, Not $ Sings x))
    question3a xA condition3a condition3b = 
        case decision [b] Sings ((assosiate xA) <*> (assosiate xA)) of 
            (Yes prf) => Left $ Evidence ((assosiate xA) <*> (assosiate xA)) 
                (condition3a  _ _ prf, prf)
            (No contra) => Right $ Evidence ((assosiate xA) <*> (assosiate xA)) 
                (\prf => contra $ condition3b  _ _ prf, contra)

    0 question3b : Decidable 1 [b] Sings => 
        Condition2a -> Condition2b ->
        Condition3a -> Condition3b ->
        Not(Exists $ \xA => (x : b) -> ((Sings $ xA <*> x) -> Sings x, Sings x -> Sings $ xA <*> x))
    question3b condition2a condition2b condition3a condition3b (Evidence xA prf) = 
        case question3a (mate xA) condition3a condition3b of 
            (Left (Evidence y (prf3, prf4))) => 
                let (prf1, prf2) = prf y
                in condition2a  _ _ prf3 $ prf2 prf4
            (Right (Evidence y (prf3, prf4))) => 
                let (prf1, prf2) = prf y
                in prf3 $ condition2b  _ _ $ prf4 . prf1
