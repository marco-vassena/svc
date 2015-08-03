-- TODO better name
-- TODO better division between 2-way partial isomorphisms and 1-way partial
-- TODO this module is not actually used, but it shows how
-- to do certain staff using Iso as primitive


module Control.Isomorphism.Partial.Util where

subset :: Alternative f => SList xs -> (HList xs -> Bool) -> Iso f xs xs
subset s p = Iso f f s s
  where f hs | p hs      = pure hs
        f hs | otherwise = empty

element :: (Alternative f, Eq a) => a -> Iso f '[ a ] '[]
element x = Iso f g (SCons SNil) SNil
  where f (Cons y _) | x == y       = pure Nil
        f _          | otherwise    = empty
        g _ = pure (hsingleton x)

inverse :: Iso f xs ys -> Iso f ys xs
inverse (Iso f g s1 s2) = Iso g f s2 s1

-- | Repeatedly apply/unapply the given isomorphism until it fails.
iterate :: Iso xs xs -> Iso xs xs
iterate step = Iso f g (sapply step) (sunapply step)
  where f = driver (pure . apply step) -- would this mean that it never stops when applied?
        g = pure . driver (unapply step)

        driver :: (HList xs -> Maybe (HList xs)) -> HList xs -> HList xs
        driver step state = maybe state (driver step) (step state)

-- Generalized fold-left for isomoprhisms.
foldl :: SList xs -> Iso (a ': xs) '[ a ] -> Iso (a ': Map [] xs) '[ a ]
foldl s i =  identity (SCons SNil)
         <.> ((identity (SCons SNil)) *** (allEmpty s))
         <.> iterate (step s i)

  where step :: SList xs -> Iso (a ': xs) '[ a ] -> Iso (a ': Map [] xs) (a ': Map [] xs)
        step s i = (i *** identity (smap proxyList s))
                <.> ((identity (SCons SNil)) *** combine s)


