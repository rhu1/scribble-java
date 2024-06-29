package org.scribble.ext.ea.codegen;

import org.scribble.core.lang.global.GProtocol;
import org.scribble.core.model.endpoint.EGraph;
import org.scribble.core.model.endpoint.EState;
import org.scribble.core.model.endpoint.EStateKind;
import org.scribble.core.model.endpoint.actions.EAction;
import org.scribble.core.type.kind.PayElemKind;
import org.scribble.core.type.name.*;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class EAAPIGen {

    public static final String SID_TYPE = "Session.Sid";
    public static final String SID_PARAM_NAME = "sid";
    public static final String ACTOR_PARAM_NAME = "actor";
    public static final String OSTATE_TYPE = "Session.OState";
    public static final String ISTATE_TYPE = "Session.IState";
    public static final String SUSPEND_TYPE = "Session.SuspendState";
    public static final String END_TYPE = "Session.End";
    public static final String SEND_PAY_PARAM_NAME = "x";
    public static final String SUSPEND_CB_PARAM_NAME = "f";
    public static final String ACTOR_SENDMESSAGE_METHOD = "sendMessage";
    public static final String ACTOR_SUSPEND_METHOD = "suspend";
    public static final String ACTOR_FINISH_METHOD = "finish";
    public static final String ACTOR_END_METHOD = "end";
    public static final String DONE_TYPE = "Done.type";
    public static final String SEALED_KW = "sealed";

    public String generateAPI(GProtocol inlined, Role r, EGraph efsm) {

        System.out.println("[EAAPIGen] Generating API for: " + inlined.fullname + "@" + r);

        EState init = efsm.init;
        Set<EState> reachable = new HashSet<>(init.getReachableStates());
        reachable.add(init);
        List<EState> ss = reachable.stream()
                .sorted(Comparator.comparingInt(o -> o.id)).toList();  // !!! TODO use order for API state numbering

        GProtoName proto = inlined.fullname.getSimpleName();
        List<Member> membs = new LinkedList<>();
        for (EState s : ss) {
            EStateKind kind = s.getStateKind();
            switch (kind) {
                case OUTPUT -> membs.add(generateOutputState(proto, r, s));
                case UNARY_RECEIVE -> membs.addAll(generateInputState(proto, r, s));
                case POLY_RECIEVE -> membs.addAll(generateInputState(proto, r, s));
                case TERMINAL -> membs.add(generateTerminalState(proto, r, s));
                default -> throw new RuntimeException("Unexpected state kind: " + kind);
            }
        }

        //return generateTop(proto, r) + "\n" + res;
        return membs.stream().map(Object::toString).collect(Collectors.joining("\n\n"));
    }

    /*// run takes Suspend if init is input
    protected GClass generateTop(GProtoName proto, Role r) {
        String name = getActorType();
        return new GClass(mods, name, params, methods, supers);
    }*/

    protected List<Member> generateInputState(GProtoName proto, Role r, EState s) {
        String susName = getSuspendTypeName(r, s);
        List<String> susMods = List.of("case");
        String actorType = getActorType(proto, r);
        List<GParam> susParams = List.of(
                new GParam(List.of(), SID_TYPE, SID_PARAM_NAME),
                new GParam(List.of(), actorType, ACTOR_PARAM_NAME));
        List<String> susSupers = List.of(SUSPEND_TYPE + "[" + actorType + "]");
        List<GMethod> susMethods = List.of();
        GClass sus = new GClass(susMods, susName, susParams, susMethods, susSupers);

        String name = getStateTypeName(r, s);
        GTrait state = new GTrait(List.of(SEALED_KW), name, List.of(ISTATE_TYPE));

        List<String> mods = susMods;
        List<GParam> params = susParams;
        List<GClass> cases = s.getDetActions().stream()
                .map(x -> new GClass(mods, getInputCaseType(r, (Op) x.mid), params, List.of(), List.of(name)))
                .toList();
        //new GClass(susMods, susName, susParams, susMethods, susSupers);

        return Stream.concat(Stream.of(sus, state), cases.stream()).toList();
    }

    protected String getInputCaseType(Role r, Op op) {
        return op.toString() + r;
    }

    protected GMethod generateSuspend(Role r, EState s) {
        String state = getStateTypeName(r, s);
        List<GParam> params = List.of(new GParam(List.of(), "", "f"));
        Function<EAction, String> f = (x) -> {
            return "\n\tif (op == \"" + x.mid + "\") {"
                    + "\n\t\t" + getInputCaseType(r, (Op) x.mid) + "(" + SID_PARAM_NAME + ", s\"${pay}\", " + getSuccTypeName(r, s, x) + "(" + SID_PARAM_NAME + ", " + ACTOR_PARAM_NAME + "))"
                    + "\n\t} else ";
        };
        String body =
                "val g = (op: String, pay: String) => {"
                        + "\n\tval msg: " + state + " ="
                        + s.getDetActions().stream().map(f::apply).collect(Collectors.joining())
                        + "\n\t{"
                        + "\n\t\tthrow new RuntimeException(s\"[ERROR] Unexpected op: ${op}(${pay})\");"
                        + "\n\tf.apply(msg)"
                        + "\n}"
                        + "\nactor.setHandler(" + SID_PARAM_NAME + ", " + r + ", g)"
                        + "\nDone";
        return new GMethod(ACTOR_SUSPEND_METHOD, params, DONE_TYPE, body);
    }

    protected Member generateOutputState(GProtoName proto, Role r, EState s) {
        String actorType = getActorType(proto, r);
        List<String> mods = List.of("case");
        String name = getStateTypeName(r, s);
        List<GParam> params = List.of(
                new GParam(List.of(), SID_TYPE, SID_PARAM_NAME),
                new GParam(List.of(), actorType, ACTOR_PARAM_NAME)
        );
        List<String> supers = List.of(OSTATE_TYPE + "[" + actorType + "]");

        List<GMethod> methods = s.getDetActions().stream()
                .map(x -> generateSend(x.peer, (Op) x.mid,
                        getPayloadType(x), getSuccTypeName(r, s, x)))
                .toList();

        return new GClass(mods, name, params, methods, supers);
    }

    protected GMethod generateSend(Role dst, Op op, DataName pay, String ret) {
        String name = "send" + op;
        List<GParam> params = List.of(new GParam(List.of(), pay.toString(), SEND_PAY_PARAM_NAME));
        String body =
                ACTOR_PARAM_NAME + "." + ACTOR_SENDMESSAGE_METHOD + "(" + SID_PARAM_NAME + ", " + dst + ", " + SEND_PAY_PARAM_NAME + ")"
                        + "\n" + ret + "(" + SID_PARAM_NAME + ", " + ACTOR_PARAM_NAME + ")";
        return new GMethod(name, params, ret, body);
    }

    protected Member generateTerminalState(GProtoName proto, Role r, EState s) {
        List<String> mods = List.of("case");
        String name = getStateTypeName(r, s);
        List<GParam> params = List.of(
                new GParam(List.of(), SID_TYPE, SID_PARAM_NAME),
                new GParam(List.of(), getActorType(proto, r), ACTOR_PARAM_NAME)
        );
        List<String> supers = List.of(END_TYPE + "[" + getActorType(proto, r) + "]");
        List<GMethod> methods = List.of(generateFinish(r));
        return new GClass(mods, name, params, methods, supers);
    }

    protected GMethod generateFinish(Role r) {
        String name = ACTOR_FINISH_METHOD;
        String body =
                "val done = super." + ACTOR_FINISH_METHOD + "(): " + DONE_TYPE + " = {"
                        + "\n\t" + ACTOR_PARAM_NAME + "." + ACTOR_END_METHOD + "(" + SID_PARAM_NAME + ", \"" + r + "\")"
                        + "\n\tdone";
        return new GMethod(name, List.of(), DONE_TYPE, body);
    }


    /* ... */

    protected DataName getPayloadType(EAction a) {
        List<PayElemType<? extends PayElemKind>> elems = a.payload.elems;
        if (elems.size() != 1) {
            throw new RuntimeException("TODO: " + elems);
        }
        PayElemType<? extends PayElemKind> fst = elems.get(0);
        if (!fst.isDataName()) {
            throw new RuntimeException("TODO: " + fst);
        }
        return (DataName) fst;
    }

    protected String getSuccTypeName(Role r, EState s, EAction a) {
        EState succ = s.getDetSuccessor(a);
        EStateKind kind = succ.getStateKind();
        return kind == EStateKind.UNARY_RECEIVE || kind == EStateKind.POLY_RECIEVE
                ? getSuspendTypeName(r, succ)
                : getStateTypeName(r, succ);
    }

    protected String getSuspendTypeName(Role r, EState s) {
        return getStateTypeName(r, s) + "Suspend";
    }

    protected String getStateTypeName(Role r, EState s) {
        return s.getStateKind() == EStateKind.TERMINAL
                ? "End" + r
                : r.toString() + s.id;
    }

    protected String getActorType(GProtoName proto, Role r) {
        return proto + "Actor" + r;
    }
}


/* ... */

interface Member { }

class GTrait implements Member {
    public final List<String> mods;
    public final String name;
    public final List<String> supers;

    public GTrait(List<String> mods, String name, List<String> supers) {
        this.mods = List.copyOf(mods);
        this.name = name;
        this.supers = List.copyOf(supers);
    }
}

class GClass implements Member {
    public final List<String> mods;
    public final String name;
    public final List<GParam> params;
    public final List<GMethod> methods;
    public final List<String> supers;

    public GClass(List<String> mods, String name, List<GParam> params,
                  List<GMethod> methods, List<String> supers) {
        this.mods = List.copyOf(mods);
        this.name = name;
        this.params = List.copyOf(params);
        this.methods = List.copyOf(methods);
        this.supers = List.copyOf(supers);
    }
}

class GMethod {
    public final String name;
    public final List<GParam> params;
    public final String ret;
    public final String body;

    public GMethod(String name, List<GParam> params, String ret, String body) {
        this.name = name;
        this.params = List.copyOf(params);
        this.ret = ret;
        this.body = body;
    }
}

class GParam {
    final List<String> mod;
    final String type;
    final String name;

    public GParam(List<String> mod, String type, String name) {
        this.mod = List.copyOf(mod);
        this.type = type;
        this.name = name;
    }
}