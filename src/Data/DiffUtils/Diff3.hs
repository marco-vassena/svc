{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Data.DiffUtils.Diff3 where

import Data.Proxy
import Data.Type.Equality
import Data.DiffUtils.Diff
import Data.DiffUtils.Diff3.Core
import Data.DiffUtils.Diff3.TypeCheck
import Data.TypeList.TList

-- | @diff3 x o y@ merges the new versions @x@ and @y@ 
-- with the base object @o@.
diff3 :: (Diff a, Diff b) => b -> a -> b -> Either [Conflict] (ES '[ a ] '[ b ])
diff3 x o y = 
  let (ox, oy) = (gdiff o x, gdiff o y) in
    case typeCheck (merge3 ox oy) of
      Left errs -> Left errs
      Right (WES ty e) ->
        case tysEq ty (TCons (proxyOf x) TNil) of
          Just Refl -> Right e
          Nothing -> Left [TConf tyErr]
            where tyErr = TyErr (ET (TCons (proxyOf x) TNil)) (toInferredType ty)

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

-- | Calls @diff3@ and if it succeds reconstruct the merged object.
diff3Patch :: (Diff a, Diff b) => b -> a -> b -> Either [Conflict] b
diff3Patch x o y = 
  case diff3 x o y of
    Left errs -> Left errs
    Right e -> Right (patch e)

