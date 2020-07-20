module Theory.Tools.IntruderRules (
    subtermIntruderRules,
    dhIntruderRules,
    bpIntruderRules,
    xorIntruderRules,
    randIntruderRules,
    multisetIntruderRules,
    mkDUnionRule,
    specialIntruderRules,
    variantsIntruder,
    isDExpRule,
    isDEMapRule,
    isDPMultRule
) where

import Control.Basics hiding (empty)
import Control.Monad.Reader

import Data.List
import qualified Data.Set as S
import Data.ByteString.Char8 (ByteString, append, pack, empty)

import Extension.Data.Label

import Utils.Mics

import Term.Maude.Signature
import Term.Narrowing.Variants.Compute
import Term.Rewriting.Norm
import Term.SubtermRule
import Term.Subsumption
import Term.Positions

import Theory.Model

specialIntruderRules :: Bool -> [IntrRuleAC]
specialIntruderRules diff =
    [ kuRule CoerceRule [kdFact x_var] (x_var) [] 
    , kuRule PubConstrRule [] (x_pub_var) [(x_pub_var)]
    , kuRule FreshConstrRule [freshFact x_fresh_var] (x_fresh_var) []
    , Rule ISendRule [kuFact x_var] [inFact x_var] [kLogFact x_var]
    ]

------------------------------------------------------------------------------
-- Rerandomizable encryption intruder rules
------------------------------------------------------------------------------

randIntruderRules ::  [IntrRuleAC]
randIntruderRules = [mkCRPkRule x_var rpk_x,
                     mkCREncRule y_var z_var x_var renc_y_z_rpkx,
                     mkCRDecRule y_var x_var rdec_y_skx,
                     mkCRRandRule y_var z_var x_var rrand_y_z_rpkx,
                     mkDRDecRule y_var z_var x_var y_var,
                     mkDRRandRule y_var z_var x_var t_var renc_y_zt_rpkx
]
    where x_var = varTerm (LVar "x" LSortMsg 0)
          y_var = varTerm (LVar "y" LSortMsg 0)
          z_var = varTerm (LVar "z" LSortMsg 0)
          t_var = varTerm (LVar "t" LSortMsg 0)
          rpk_x = fAppNoEq rpkSym [x_var]
          zt_radd = fAppAC RAdd [z_var, t_var]
          renc_y_z_rpkx = fAppNoEq rencSym [y_var, z_var, rpk_x]
          rdec_y_skx = fAppNoEq rdecSym [y_var, x_var]
          rrand_y_z_rpkx = fAppNoEq rrandSym [y_var, z_var, rpk_x]
          renc_y_zt_rpkx = fAppNoEq rencSym [y_var, zt_radd, rpk_x]
                       -- TODO: add constructor rules for all functions (renc, rdec, rpk, rrand)
                       --       add two deconstruction rules: one for rdec(renc(...)) (unlimited applications)
                       --                               , and one for rrand(renc(...)) (limited to one application)

-- rrand(renc(m, r1, pk(sk)), r2, pk(sk)) = renc(m, radd(r1, r2), pk(sk))
mkDRRandRule :: LNTerm -> LNTerm -> LNTerm -> LNTerm -> LNTerm -> IntrRuleAC
mkDRDecRule t_prem t_prem2 t_prem3 t_prem4 t_conc =
    Rule (DestrRule (append (pack "_") rrandSymString)) 1 True False
         [kdFact $ fAppNoEq rencSym [t_prem, t_prem2, t_prem3],
          kuFact t_prem3, kuFact t_prem4]
        [kdFact t_conc]] [] []
        
-- rdec(renc(m, r, pk(sk)), sk) = m
-- (m, r, sk)
mkDRDecRule :: LNTerm -> LNTerm -> LNTerm -> LNTerm -> IntrRuleAC
mkDRDecRule t_prem t_prem2 t_prem3 t_conc =
    Rule (DestrRule (append (pack "_") ) rdecSymString) 0 True False
         [kdFact $ fAppNoEq rencSym [t_prem, t_prem2, t_prem3_pk], kuFact t_prem3]
         [kdFact t_conc] [] []
    where
        t_prem3_pk = fAppNoEq rpkSym [t_prem3]

mkCRPkRule :: LNTerm -> LNTerm -> IntrRuleAC
mkCRPkRule t_prem t_conc =
    Rule (ConstrRule (append (pack "_") rpkSymString))
         [kuFact t_prem] 
         [kuFact t_conc] [kuFact t_conc] []

mkCREncRule :: LNTerm -> LNTerm -> LNTerm -> LNTerm -> IntrRuleAC
mkCREncRule t_prem t_prem2 t_prem3 t_conc =
    Rule (ConstrRule (append (pack "_") rencSymString))
         [kuFact t_prem, kuFact t_prem2, kuFact $ fAppNoEq rpkSym [t_prem3]]
         [kuFact t_conc] [kuFact t_conc] []

mkCRRandRule :: LNTerm -> LNTerm -> LNTerm -> LNTerm -> IntrRuleAC
mkCRRandRule t_prem t_prem2 t_prem3 t_conc =
    Rule (ConstrRule (append (pack "_") rrandSymString))
         [kuFact t_prem, kuFact t_prem2, kuFact $ fAppNoEq rpkSym [t_prem3]]
         [kuFact t_conc] [kuFact t_conc] []

mkCRDecRule :: LNTerm -> LNTerm -> LNTerm -> IntrRuleAC
mkCRDecRule t_prem t_prem2 t_conc =
    Rule (ConstrRule (append (pack "_") rdecSymString))
         [kuFact t_prem, kuFact t_prem2]
         [kuFact t_conc] [kuFact t_conc] []

