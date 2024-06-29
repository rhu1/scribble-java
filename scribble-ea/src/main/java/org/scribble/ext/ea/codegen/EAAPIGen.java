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

        System.out.println("\n[EAAPIGen] Generating API for: " + inlined.fullname + "@" + r);

        EState init = efsm.init;
        Set<EState> reachable = new HashSet<>(init.getReachableStates());
        reachable.add(init);
        List<EState> ss = reachable.stream()
                .sorted(Comparator.comparingInt(o -> o.id)).toList();  // !!! TODO use order for API state numbering

        GProtoName proto = inlined.fullname.getSimpleName();
        List<Member> membs = new LinkedList<>();
        membs.add(new GPackage("tmp.scratch.scratch07.foo"));
        membs.add(new GImport("tmp.scratch.scratch07.eventactor", List.of("Actor", "Done", "Session")));
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
        return membs.stream().map(Member::toString).collect(Collectors.joining("\n\n"));
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
        List<GMethod> susMethods = List.of(generateSuspend(r, s));
        GClass sus = new GClass(susMods, susName, susParams, susMethods, susSupers);

        String name = getStateTypeName(r, s);
        GTrait state = new GTrait(List.of(SEALED_KW), name, List.of(ISTATE_TYPE));

        List<String> mods = susMods;
        List<GParam> params = List.of(
                new GParam(List.of(), SID_TYPE, SID_PARAM_NAME),
                new GParam(List.of(), "String", SEND_PAY_PARAM_NAME));
        //new GParam(List.of(), getSuccTypeName(r, s, x), "s"));
        List<GClass> cases = s.getDetActions().stream()
                .map(x -> new GClass(mods, getInputCaseType(r, (Op) x.mid),
                        //params,
                        Stream.concat(params.stream(), Stream.of(new GParam(List.of(), getSuccTypeName(r, s, x), "s"))).toList(),
                        List.of(), List.of(name)))
                .toList();
        //new GClass(susMods, susName, susParams, susMethods, susSupers);

        return Stream.concat(Stream.of(sus, state), cases.stream()).toList();
    }

    protected String getInputCaseType(Role r, Op op) {
        return op.toString() + r;
    }

    protected GMethod generateSuspend(Role r, EState s) {
        String state = getStateTypeName(r, s);
        List<GParam> params = List.of(new GParam(List.of(), state + " => " + DONE_TYPE, "f"));
        Function<EAction, String> f = (x) -> {
            return "\n\tif (op == \"" + x.mid + "\") {"
                    + "\n\t\t" + getInputCaseType(r, (Op) x.mid) + "(" + SID_PARAM_NAME + ", s\"${pay}\", " + getSuccTypeName(r, s, x) + "(" + SID_PARAM_NAME + ", " + ACTOR_PARAM_NAME + "))"
                    + "\n\t} else ";
        };
        String body =
                "val g = (op: String, pay: String) => {"
                        + "\n\tval msg: " + state + " ="
                        + s.getDetActions().stream().map(f::apply).collect(Collectors.joining())
                        + "{"
                        + "\n\t\tthrow new RuntimeException(s\"[ERROR] Unexpected op: ${op}(${pay})\");"
                        + "\n}"
                        + "\nf.apply(msg)"
                        + "\n}"
                        + "\nactor.setHandler(" + SID_PARAM_NAME + ", \"" + r + "\", g)"
                        + "\nDone";
        return new GMethod(List.of(), ACTOR_SUSPEND_METHOD, params, DONE_TYPE, body);
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
                "\t" + ACTOR_PARAM_NAME + "." + ACTOR_SENDMESSAGE_METHOD + "(" + SID_PARAM_NAME + ", \"" + dst + "\", \"" + op + "\", " + SEND_PAY_PARAM_NAME + ")"
                        + "\n\t" + ret + "(" + SID_PARAM_NAME + ", " + ACTOR_PARAM_NAME + ")";
        return new GMethod(List.of(), name, params, ret, body);
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
                "val done = super." + ACTOR_FINISH_METHOD + "()"
                        + "\n\t" + ACTOR_PARAM_NAME + "." + ACTOR_END_METHOD + "(" + SID_PARAM_NAME + ", \"" + r + "\")"
                        + "\n\tdone";
        return new GMethod(List.of("override"), name, List.of(), DONE_TYPE, body);
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
        //return proto + "Actor" + r;
        return "Actor";  // !!!
    }
}


/* ... */

interface Member {
    String toString(String pref);
}

class GPackage implements Member {
    public final String name;

    public GPackage(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public String toString(String pref) {
        return pref + "package " + this.name;
    }
}

class GImport implements Member {
    public final String pref;  // no trailing "."
    public final List<String> names;  // non-empty

    public GImport(String pref, List<String> names) {
        this.pref = pref;
        this.names = List.copyOf(names);
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public String toString(String pref) {
        return pref + "import " + this.pref + "."
                + (this.names.size() == 1 ? this.names.get(0) : "{" + this.names.stream().collect(Collectors.joining(", ")) + "}");
    }
}

class GTrait implements Member {
    public final List<String> mods;
    public final String name;
    public final List<String> supers;

    public GTrait(List<String> mods, String name, List<String> supers) {
        this.mods = List.copyOf(mods);
        this.name = name;
        this.supers = List.copyOf(supers);
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public String toString(String pref) {
        return pref + this.mods.stream().collect(Collectors.joining(" ")) + " trait " + this.name
                + (this.supers.isEmpty() ? "" : " extends " + supers.stream().collect(Collectors.joining(", ")));
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

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public String toString(String pref) {
        return pref + this.mods.stream().collect(Collectors.joining(" ")) + " class " + this.name + "(" + this.params.stream().map(GParam::toString).collect(Collectors.joining(", ")) + ")"
                + (this.supers.isEmpty() ? "" : " extends " + supers.stream().collect(Collectors.joining(", ")))
                + (this.methods.isEmpty() ? "" :
                " {\n" + pref + this.methods.stream().map(x -> x.toString(pref + "\t")).collect(Collectors.joining("\n\n")) + "\n}");
    }
}

class GMethod implements Member {
    public final List<String> mods;
    public final String name;
    public final List<GParam> params;
    public final String ret;
    public final String body;

    public GMethod(List<String> mods, String name, List<GParam> params, String ret, String body) {
        this.mods = List.copyOf(mods);
        this.name = name;
        this.params = List.copyOf(params);
        this.ret = ret;
        this.body = body;
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public String toString(String pref) {
        return pref + (this.mods.isEmpty() ? "" : this.mods.stream().collect(Collectors.joining(" ")) + " ") + "def " + this.name + "(" + this.params.stream().map(GParam::toString).collect(Collectors.joining(", ")) + "): " + this.ret + " = {"
                + "\n" + pref + this.body.replaceAll("\\n", "\n" + pref)
                + "\n" + pref + "}";
    }
}

class GParam {
    final List<String> mods;
    final String type;
    final String name;

    public GParam(List<String> mods, String type, String name) {
        this.mods = List.copyOf(mods);
        this.type = type;
        this.name = name;
    }

    @Override
    public String toString() {
        return this.mods.stream().collect(Collectors.joining(" "))
                + " " + this.name + ": " + this.type;
    }
}