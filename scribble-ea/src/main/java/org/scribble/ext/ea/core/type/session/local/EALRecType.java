package org.scribble.ext.ea.core.type.session.local;

import org.jetbrains.annotations.NotNull;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.session.local.LType;

import java.util.Map;
import java.util.Optional;

public class EALRecType implements EALType {

    @NotNull public final RecVar var;
    @NotNull public final EALType body;

    protected EALRecType(@NotNull RecVar var, @NotNull EALType body) {
        this.var = var;
        this.body = body;
    }

    @Override
    public EALType concat(EALType t) {
        throw new RuntimeException("Concat not defined for recursion");
    }

    @Override
    public EALType subs(Map<RecVar, EALRecType> map) {
        return map.containsKey(this.var)
                ? this  // !!! FIXME doesn't support shadowing
                : new EALRecType(this.var, this.body.subs(map));
    }

    @Override
    public EALType unfoldAllOnce() {
        EALType rt = this;
        while (rt instanceof EALRecType) {
            EALRecType cast = (EALRecType) rt;
            rt = this.body.subs(Map.of(cast.var, cast));
        }
        return rt;
    }

    /*@Override
    public EALType unfold() {
        return unfold(this.var, this.body);
    }*/

    @Override
    public EALType unfold(RecVar rvar, EALType t) {
        return this.var.equals(rvar)
                ? this.body.unfold(rvar, t)  // Expected: this.body.equals(t)
                : new EALRecType(this.var, this.body.unfold(rvar, t));
    }

    @Override
    public Optional<EALType> step(LType a) {
        //throw new RuntimeException("Shouldn't get here (manual unfolded type annots): " + this + "\n\t" + a);
        return unfoldAllOnce().step(a);  // cf. EAPConfig delta.map.get(k).unfoldAllOnce();  // !!! cf. EAPSystem this.annots.map.get(k2) -- use unfolded as annot -- XXX that only allows that many number of unfoldings during execution
    }

    /* Aux */

    @Override
    public String toString() {
        return "\u03bc" + this.var + "." + this.body;
    }

    /* equals/canEquals, hashCode */

    @Override
    public boolean equals(Object o) {
        if (this == o) { return true; }
        if (o == null || getClass() != o.getClass()) { return false; }
        EALRecType them = (EALRecType) o;
        return them.canEquals(this)
                && this.var.equals(them.var) && this.body.equals(them.body);
    }

    @Override
    public boolean canEquals(Object o) {
        return o instanceof EALRecType;
    }

    @Override
    public int hashCode() {
        int hash = EALType.REC_HASH;
        hash = 31 * hash + this.var.hashCode();
        hash = 31 * hash + this.body.hashCode();
        return hash;
    }
}
