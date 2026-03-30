module TheMasterForest

import Decidable.Equality
import Decidable.Equality.Core

data SKIExpr : Type where
    Var : Char -> SKIExpr
    S : SKIExpr
    K : SKIExpr
    I :SKIExpr
    (<*>) : SKIExpr -> SKIExpr ->SKIExpr

data VarOccurs : Char -> SKIExpr -> Type where 
    VarOccursVar : VarOccurs c (Var c)
    VarOccursCongL : VarOccurs c x -> VarOccurs c (x <*> y)
    VarOccursCongR : VarOccurs c y -> VarOccurs c (x <*> y)

varOccurs : (c : Char) -> (e : SKIExpr) -> Dec(VarOccurs c e)
varOccurs c (Var d) = 
    case decEq c d of 
        (Yes eq) => Yes $ rewrite eq in VarOccursVar
        (No contra) => No $ \VarOccursVar => contra Refl
varOccurs c S = No $ \prf impossible
varOccurs c K = No $ \prf impossible
varOccurs c I = No $ \prf impossible
varOccurs c (x <*> y) = 
    case varOccurs c x of 
        (Yes prf) => Yes $ VarOccursCongL prf
        (No contra1) =>
            case varOccurs c y of 
                (Yes prf) => Yes $ VarOccursCongR prf
                (No contra2) => No $ \prf => 
                    case prf of 
                        (VarOccursCongL prf') => contra1 prf'
                        (VarOccursCongR prf') => contra2 prf'

data SameExpr : SKIExpr -> SKIExpr -> Type where
    SameS : SameExpr (S <*> x <*> y <*> z) (x <*> z <*> (y <*> z))
    SameK : SameExpr (K <*> x <*> y) x
    SameI : SameExpr (I <*> x) x
    SameRefl : SameExpr x x
    SameTrans : SameExpr x y -> SameExpr y z -> SameExpr x z
    SameCong : SameExpr x y -> SameExpr z w -> SameExpr (x <*> z) (y <*> w)

alphaEliminate : (c : Char) -> (e : SKIExpr) -> (e' ** (SameExpr (e' <*> Var c) e, Not $ VarOccurs c e'))
alphaEliminate c (Var d) = 
    case decEq c d of 
        (Yes eq) => (I ** (rewrite eq in SameI, \prf impossible)) --principles 1 
        (No contra) => (K <*> (Var d) ** 
            (SameK,  \(VarOccursCongR VarOccursVar) => contra Refl))
alphaEliminate c S = 
    (K <*> S ** 
        (SameK, 
        \prf => 
            case prf of 
                (VarOccursCongL VarOccursVar) impossible
                (VarOccursCongL (VarOccursCongL x)) impossible
                (VarOccursCongL (VarOccursCongR x)) impossible
                (VarOccursCongR VarOccursVar) impossible
                (VarOccursCongR (VarOccursCongL x)) impossible
                (VarOccursCongR (VarOccursCongR x)) impossible))
alphaEliminate c K = 
    (K <*> K ** 
        (SameK, 
        \prf => 
            case prf of 
                (VarOccursCongL VarOccursVar) impossible
                (VarOccursCongL (VarOccursCongL x)) impossible
                (VarOccursCongL (VarOccursCongR x)) impossible
                (VarOccursCongR VarOccursVar) impossible
                (VarOccursCongR (VarOccursCongL x)) impossible
                (VarOccursCongR (VarOccursCongR x)) impossible))
alphaEliminate c I = 
    (K <*> I ** 
        (SameK, 
        \prf => 
            case prf of 
                (VarOccursCongL VarOccursVar) impossible
                (VarOccursCongL (VarOccursCongL x)) impossible
                (VarOccursCongL (VarOccursCongR x)) impossible
                (VarOccursCongR VarOccursVar) impossible
                (VarOccursCongR (VarOccursCongL x)) impossible
                (VarOccursCongR (VarOccursCongR x)) impossible))
alphaEliminate c x@(y <*> z) = 
    case varOccurs c x of 
        (Yes prf) => 
            case varOccurs c y of 
                (Yes prf') => 
                    let (y' ** (prf1, prf2)) = alphaEliminate c y
                        (z' ** (prf3, prf4)) = alphaEliminate c z
                    in (S <*> y' <*> z' ** 
                        (SameTrans SameS $ SameCong prf1 prf3, 
                        \prf => 
                            case prf of 
                                (VarOccursCongL (VarOccursCongR prf')) => prf2 prf'
                                (VarOccursCongR prf') => prf4 prf'))
                (No contra) => 
                    case z of 
                        (Var d) => (y ** 
                            (SameCong 
                                SameRefl $
                                case prf of 
                                    (VarOccursCongL prf') => void $ contra prf'
                                    (VarOccursCongR VarOccursVar) => SameRefl, 
                            contra))
                        _ => 
                            let (y' ** (prf1, prf2)) = alphaEliminate c y
                                (z' ** (prf3, prf4)) = alphaEliminate c z
                            in (S <*> y' <*> z' ** 
                                (SameTrans SameS $ SameCong prf1 prf3, 
                                \prf => 
                                    case prf of 
                                        (VarOccursCongL (VarOccursCongR prf')) => prf2 prf'
                                        (VarOccursCongR prf') => prf4 prf'))
        (No contra) => 
            (K <*> (y <*> z) ** 
                (SameK, 
                \prf => 
                    case prf of 
                        (VarOccursCongL prf') impossible
                        (VarOccursCongR prf') => contra prf'))

-- eliminate : List Char -> SKIExpr ->SKIExpr
-- eliminate [] x = x
-- eliminate (c :: cs) x = eliminate cs $ alphaEliminate c x

expr = Var 'y' <*> Var 'x'