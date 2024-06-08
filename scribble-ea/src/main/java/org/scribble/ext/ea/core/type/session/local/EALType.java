package org.scribble.ext.ea.core.type.session.local;

import org.scribble.core.type.name.Op;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.session.local.LSend;
import org.scribble.core.type.session.local.LType;
import org.scribble.ext.ea.core.type.EAType;
import org.scribble.ext.ea.core.type.value.EAVType;
import org.scribble.util.Pair;

import java.util.Map;
import java.util.Optional;

public interface EALType extends EAType {

    int IO_HASH = 11003;
    int IN_HASH = 11027;
    int OUT_HASH = 11047;
    int REC_HASH = 11057;
    int END_HASH = 11059;
    int RECVAR_HASH = 11069;

    /* ... */

    // !!! FIXME TODO Optional
    // !!! currently not used consistently (added ad hoc from testing)
    // Currently only unfolding -- so currently symmetric
    // ...found is expr, required is usually pre
    static void equalSubFold(EALType found, EALType required) {  // equals up to (asymmetric) subtype-like unfolding
        /*if (!(found.equals(required) || found.unfoldAllOnce().equals(required.unfoldAllOnce()))) {
            throw new RuntimeException("Incompatible pre type:\n"
                    + "\tfound=" + found + ", required=" + required);
        }*/
        if (found == null || required == null) {
            throw new RuntimeException("Null: " + found + " ,, " + required);
        }

        if (found instanceof EALEndType) {
            if (found.equals(required)) {
                return;
            }
        } else if (found instanceof EALRecVarType) {
            if (found.equals(required)) {
                return;
            }
        } else if (found instanceof EALRecType) {
            if (found.equals(required) || found.unfoldAllOnce().equals(required.unfoldAllOnce())) {
                return;
            }
            //System.out.println("2222222: " + found + "\n\t" + found.unfoldAllOnce() + "\n\t" + required + "\n\t" + required.unfoldAllOnce());
            //System.out.println("2222222: " + found.unfoldAllOnce().equals(required.unfoldAllOnce()));
            equalSubFold(found.unfoldAllOnce(), required);  // XXX potentially non terminating when not equals-unfold
            return;
        } else if (required instanceof EALRecType) {
            if (found.equals(required) || found.unfoldAllOnce().equals(required.unfoldAllOnce())) {
                return;
            }
            equalSubFold(found, required.unfoldAllOnce());  // XXX potentially non terminating when not equals-unfold
            return;
        } else if (found instanceof EALTypeIOBase) {
            if (found.equals(required) || found.unfoldAllOnce().equals(required.unfoldAllOnce())) {
                return;
            }
            //System.out.println("1111111111: " + found + "\n\t" + found.unfoldAllOnce() + "\n\t" + required + "\n\t" + required.unfoldAllOnce());
            //System.out.println("1111111111: " + found.unfoldAllOnce().equals(required.unfoldAllOnce()));
            Map<Op, Pair<EAVType, EALType>> c1 = ((EALTypeIOBase) found).cases;
            Map<Op, Pair<EAVType, EALType>> c2 = ((EALTypeIOBase) required).cases;
            if (!c1.keySet().equals(c2.keySet())) {
                throw new RuntimeException("Incompatible pre type:\n"
                        + "\tfound=" + found + ", required=" + required);
            }
            for (Op op : c1.keySet()) {
                equalSubFold(c1.get(op).right, c2.get(op).right);
            }
            return;
        } else {
            throw new RuntimeException("Incompatible pre type:\n"
                    + "\tfound=" + found + ", required=" + required);
        }
    }

    /* ... */

    // S^?
    static boolean isInType(EALType t) {
        return t instanceof EALInType || t.unfoldAllOnce() instanceof EALInType;
    }

    //boolean wellFormed();  // TODO bound rec labels, no self send -- operationally OK if async

    EALType concat(EALType t);

    EALType subs(Map<RecVar, EALRecType> map);

    EALType unfoldAllOnce();

    @Deprecated
    EALType unfold(RecVar rvar, EALType t);

    /* ... */

    // cf. LTS on Delta type envs
    Optional<EALType> step(LType a);  // TODO Either
}
