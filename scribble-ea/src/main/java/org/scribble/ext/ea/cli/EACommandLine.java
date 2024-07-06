package org.scribble.ext.ea.cli;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;
import org.scribble.cli.CLFlags;
import org.scribble.cli.CommandLine;
import org.scribble.cli.CommandLineException;
import org.scribble.core.job.Core;
import org.scribble.core.job.CoreArgs;
import org.scribble.core.job.CoreContext;
import org.scribble.core.lang.global.GProtocol;
import org.scribble.core.model.endpoint.EGraph;
import org.scribble.core.type.name.GProtoName;
import org.scribble.core.type.name.Role;
import org.scribble.ext.ea.codegen.EAApiGen;
import org.scribble.ext.ea.core.runtime.*;
import org.scribble.ext.ea.core.runtime.config.EACActor;
import org.scribble.ext.ea.core.term.EATerm;
import org.scribble.ext.ea.core.term.EATermFactory;
import org.scribble.ext.ea.core.term.comp.EAComp;
import org.scribble.ext.ea.core.term.expr.EAEAPName;
import org.scribble.ext.ea.core.term.expr.EAExpr;
import org.scribble.ext.ea.core.type.EATypeFactory;
import org.scribble.ext.ea.core.type.Gamma;
import org.scribble.ext.ea.core.type.GammaState;
import org.scribble.ext.ea.core.type.session.local.Delta;
import org.scribble.ext.ea.core.type.session.local.EALType;
import org.scribble.ext.ea.core.type.value.EAVType;
import org.scribble.ext.ea.parser.antlr.EACalculusLexer;
import org.scribble.ext.ea.parser.antlr.EACalculusParser;
import org.scribble.ext.ea.util.*;
import org.scribble.job.Job;
import org.scribble.job.JobContext;
import org.scribble.util.*;

import java.util.*;
import java.util.stream.Collectors;


//- key point: only "relevant" handlers available at any one time -- cf. prev EDP works (all handlers all the time)

// HERE
//- check getFoo for input side -- generalise for async
//- "unify" handlers and lambdas/recs
//- recursion -- add rec vars
//- separate P vals from terms AST
//- rename pairs->endpoints, triples->"handlers"
//- Need G/L annotations on restr in op sem with updating -- currently EAPSystem.type takes Delta as "manual" arg (add types as EAPSystem fields)
//- Consider async
//- add type method to System, split delta by configs key (endpoints)
//- TEST config typing with handrolled Deltas -- as opposed to T-Session introducing each endpoint to Delta -- also because env splitting is not algorithmic
//- finish testing infer for subset, but then do initiation and top-down register type annot
//- types for subset, initiation+types, if-then-else
//- if-else
//- configs and config exec
//- newAP/spawn/register


		/*%%   p (+) { l1(A) -> p & { ... }, l2(B) -> p (+) { l3(C) -> End } }
%%   let () <=
%%       if rand () then
%%           p ! l1(V);
%%           suspend h1 -- p (+) { l3(C) -> End }
%%       else
%%           p ! l2(W) -- p (+) { l3(C) -> End }
%%   in
%%   -- p (+) { l3(C) -> End }
%%   print("still alive")*/






// Includes assrt-core functionality (all extra args are currently for assrt-core)
public class EACommandLine extends CommandLine {

    public EACommandLine(String... args) {
        super(args);
    }

    public static void main(String[] args)
            throws CommandLineException, AntlrSourceException {

        ////CommandLine.main(args);
        new EACommandLine(args).run();
        //eamain();  // !!! base CommandLine fully bypassed -- No main module used

        ////testParser();
    }

    @Override
    protected CLFlags newCLFlags() {
        return new EACLFlags();
    }

    // A Scribble extension should override as appropriate
    // TODO: rename, barrier misleading (sounds like a sync)
    @Override
    protected void tryBarrierTask(Job job, Pair<String, String[]> task)
            throws ScribException, CommandLineException {
        switch (task.left) {
            case EACLFlags.EA_API_GEN_FLAG: {
                JobContext jobc = job.getContext();
                GProtoName fullname = checkGlobalProtocolArg(jobc, task.right[0]);
                //Map<String, String> out = jgen.generateSessionApi(fullname);* /
                //System.out.println("aaaaaaa: " + task.left + ",, " + fullname);
                Core core = job.getCore();
                CoreContext corec = core.getContext();
                GProtocol inlined = corec.getInlined(fullname);
                for (Role r : inlined.roles) {
                    EGraph efsm = job.config.args.get(CoreArgs.MIN_EFSM)
                            ? corec.getMinimisedEGraph(fullname, r)
                            : corec.getEGraph(fullname, r);
                    foo(inlined, r, efsm);
                }
                break;
            }
            default:
                super.tryBarrierTask(job, task);
        }
    }

    protected void foo(GProtocol inlined, Role r, EGraph efsm) {
        EAApiGen gen = new EAApiGen();
        System.out.println("\n" + gen.generateAPI(inlined, r, efsm));
    }

    private static void eamain() {

        /* HERE HERE  // merge rhu1-refactorinterfaces -- i.e., latest scrib-core

        - ...sys/actor/thread typing return Either
        - ...testing summary
        - ...eval Optional/Either return
        - ...Right @NotNull (no Void)
        - ...terms in derivations

        - ...fidelity/coherence -- cf. EAPSystem.annots -- after async
        - ...Optional (cf. canX)
        - ...wild S' in suspend typing
        - ...need (self) handler firing when state satis some condition -- !!! how done in standard actors?
        - ...evolving state types? but tricky if state is config-wide (shared by multiple sessions)

        - add state to return
        - refactor EAPVal as EAPPure -- separate packages for expr/pure -- distinguish actual val from pure
        - separate isGround/isValue -- cf. canBeta for exprs vs. is-stuck
        - fix canBeta contexts and isGround for all exprs
        - tidy foo vs. beta -- cf. some expr foo is just beta (some not, e.g., let)
        */

        EATest.tests();
    }


    /* ... */

    public static void typeCheckComp(GammaState gamma, EAComp M, EALType pre) {
        System.out.print("Typing computation: " + M);
        Either<Exception, Pair<Pair<EAVType, EALType>, Tree<String>>> typingA = M.type(gamma, pre);
        if (typingA.isLeft()) {
            throw new RuntimeException(typingA.getLeft());
        }
        Pair<Pair<EAVType, EALType>, Tree<String>> ppA = typingA.getRight();
        System.out.println(" " + pre + " ,, " + ppA.left + "\n" + ppA.right);
    }

    public static void typeCheckExpr(GammaState gamma, EAExpr e, EAVType A) {
        System.out.print("Typing expr: " + e);
        Either<Exception, Pair<EAVType, Tree<String>>> t = e.type(gamma);
        if (t.isLeft()) {
            throw new RuntimeException(t.getLeft());
        }
        Pair<EAVType, Tree<String>> p = t.getRight();
        System.out.println(" " + p.left + "\n" + p.right);
        if (!p.left.equals(A)) {
            throw new RuntimeException("Type checking error, expected: " + A);
        }
    }

    public static void typeCheckActor(EACActor c, Delta delta) {  // TODO deprecate
        typeCheckActor(c, new Gamma(), delta);
    }

    public static void typeCheckActor(EACActor c, Gamma gamma, Delta delta) {
        System.out.println("Typing actor: [T-Actor] " + gamma + "; " + delta
                + ConsoleColors.VDASH + " " + c);
        Either<Exception, Tree<String>> t = c.type(gamma, delta);
        if (t.isLeft()) {
            throw new RuntimeException("Not well typed:\n", t.getLeft());
        }
    }

    /* ... */

    public static void typeCheckSystem(EAAsyncSystem sys) {  // TODO refactor
        typeCheckSystem(sys, new Gamma());
    }

    public static void typeCheckSystem(EAAsyncSystem sys, Gamma gamma) {
        typeCheckSystem(sys, false, gamma);
    }

    public static void typeCheckSystem(EAAsyncSystem sys, boolean debug, Gamma gamma) {
        typeCheckSystem(sys, debug, "", gamma);
    }

    public static Optional<Exception> typeCheckSystem(
            EAAsyncSystem sys, boolean debug, String indent, Gamma gamma) {
        if (debug) {
            System.out.println(indent + "Type checking system:");
        }
        Either<Exception, List<Tree<String>>> t = sys.type(gamma);
        if (t.isLeft()) {
            return Optional.of(t.getLeft());
        }
        if (debug) {
            System.out.println(t.getRight().stream()  // !!!
                    .map(x -> x.toString(indent + "  "))
                    .collect(Collectors.joining("\n\n")));
        }
        return Optional.empty();
    }

    /* ... */

    //static int state = 0;

    public static class Bounds {

        public final int maxDepth;  // -1 for unbounded
        private int state = 0;
        private final Set<EAAsyncSystem> seen = EAUtil.setOf();  // TODO make state id map

        public Bounds(int maxDepth) { this.maxDepth = maxDepth; }

        public int getState() { return state++; }

        public void addSys(EAAsyncSystem sys) { this.seen.add(sys); }

        public boolean isDepthPrune(int depth) {
            return this.maxDepth >= 0 && depth >= this.maxDepth;
        }

        // !!! currently pruning only iotas (not sess names, spawn pids, etc)
        public boolean isSeenPrune(EAAsyncSystem sys) {
            //return this.seen.contains(sys);
            //return this.seen.stream().anyMatch(x -> x.equals(sys) || EAAsyncSystem.unifyIotas(x, sys));
            for (EAAsyncSystem x : this.seen) {
                if (x.equals(sys)) {
                    return true;
                } else if (EAAsyncSystem.unifyIotas(x, sys)) {
                    System.err.println("[Debug] Unified and pruned:\n" + x + "\n" + sys + "\n");
                    return true;
                }
            }
            return false;
        }
    }

    public static final Scanner KB = new Scanner(System.in);

    // TODO refactor
    // bounds max depth -1 for unbounded
    public static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> typeAndRun(
            EAAsyncSystem sys, boolean debug, Bounds bounds) {
        return typeAndRun(sys, debug, bounds, false, new Gamma());
    }

    public static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> typeAndRun(
            EAAsyncSystem sys, boolean debug, Bounds bounds, Gamma gamma) {
        return typeAndRun(sys, debug, bounds, false, gamma);
    }

    public static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> typeAndRun(
            EAAsyncSystem sys, boolean debug, Bounds bounds, boolean interactive, Gamma gamma) {
        Set<EAAsyncSystem> terminals = EAUtil.setOf();

        //state = 0;
        System.out.println("\n(" + bounds.state + ") Initial system:\n" + sys);
        Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> res =
                typeAndRunDAux(sys, 0, debug, "", bounds, terminals, interactive, gamma);

        /*System.out.println("\nTerminals:");
        for (EAAsyncSystem term : terminals) {
            System.out.println("\n" + term);
        }*/

        return res;
    }

    // Right = (Pruned, Terminals)
    public static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> typeAndRunDAux(
            EAAsyncSystem sys, int depth, boolean debug, String indent, Bounds bounds,
            Set<EAAsyncSystem> terminals,  // TODO refactor
            boolean interactive,
            Gamma gamma
    ) {

        if (bounds.isSeenPrune(sys)) {  // Check first before depth prune
            System.out.println(indent + "Already seen.");
            return Either.right(Pair.of(EAUtil.setOf(), EAUtil.setOf()));
        }

        Optional<Exception> opt = typeCheckSystem(sys, debug, indent, gamma);
        if (opt.isPresent()) {
            return Either.left(opt.get());
        }

        if (bounds.isDepthPrune(depth)) {
            System.out.println(indent + "Pruned at depth: " + depth);
            return Either.right(Pair.of(EAUtil.setOf(sys), EAUtil.setOf()));
        }
        bounds.addSys(sys);

        //Map<EAPid, Map<EASid, Either<EAComp, EAMsg>>> pids = sys.getSteppable();
        //Map<EAPid, Either<Map<EASid, Either<EAComp, EAMsg>>, Set<EAComp>>> pids = sys.getSteppable();
        Pair<
                Map<EAPid, Either<Map<EASid, Either<EAComp, EAMsg>>, Set<EAComp>>>,
                Set<Pair<EAEAPName, Map<EAPid, Pair<Role, EAIota>>>>> steppa =
                sys.getSteppable();
        System.out.println(indent + "Steppable: " + steppa);
        Map<EAPid, Either<Map<EASid, Either<EAComp, EAMsg>>, Set<EAComp>>> pids = steppa.left;
        Set<Pair<EAEAPName, Map<EAPid, Pair<Role, EAIota>>>> inits = steppa.right;

        if (pids.isEmpty() && inits.isEmpty()) {
            /*if (!debug) {
                System.out.println();
                System.out.println(indent + "Result steps(" + depth + "):");
                System.out.println(sys);
            }*/
            //terminals.add(sys);  // TODO also record depth-pruned states (not validated)
            if (sys.actors.values().stream().anyMatch(x -> !x.T.isIdle() || !x.sigma.isEmpty())) {
                return Either.left(new Exception(indent + "Stuck: " + sys));
            }
            return Either.right(Pair.of(EAUtil.setOf(), EAUtil.setOf(sys)));
        }

        // !pids.isEmpty()
        int stmp = bounds.state;
        int i = 0;
        Set<EAAsyncSystem> depthPruned = EAUtil.setOf();
        Set<EAAsyncSystem> terminals1 = EAUtil.setOf();
        //for (Map.Entry<EAPid, Map<EASid, Either<EAComp, EAMsg>>> pid : pids.entrySet()) {
        for (Map.Entry<EAPid, Either<Map<EASid, Either<EAComp, EAMsg>>, Set<EAComp>>> pid : pids.entrySet()) {
            EAPid p = pid.getKey();
            Either<Map<EASid, Either<EAComp, EAMsg>>, Set<EAComp>> v = pid.getValue();

            Either<Exception, Triple<EAAsyncSystem, Tree<String>, Tree<String>>> step;
            System.out.print("\n" + indent + "(" + stmp + "-" + i + ") ");
            if (v.isLeft()) {
                //Map.Entry<EASid, Either<EAComp, EAMsg>> sid = pid.getValue().entrySet().iterator().next();  // FIXME execute all
                Map.Entry<EASid, Either<EAComp, EAMsg>> sid = v.getLeft().entrySet().iterator().next();  // FIXME execute all
                EASid s = sid.getKey();  // Only needed for debug out?
                Either<EAComp, EAMsg> a = sid.getValue();
                if (a.isLeft()) {
                    EAComp e = a.getLeft();
                    System.out.println("Stepping " + s + "@" + p + ": " + e);
                    step = sys.step(p, s, e);
                } else {
                    EAMsg m = a.getRight();
                    System.out.println("Reacting " + s + "@" + p + ": " + m);
                    step = sys.react(p, s, m);
                }

            } else {
                Set<EAComp> nosess = v.getRight();
                EAComp a = nosess.iterator().next();  // CHECKME Set needed? (if so, execute all)

                System.out.println("Stepping " + p + ": " + a);
                step = sys.step(p, null, a);  // FIXME HACK state s
            }

            if (step.isLeft()) {
                throw new RuntimeException(step.getLeft());
            }
            Triple<EAAsyncSystem, Tree<String>, Tree<String>> get = step.getRight();
            bounds.state++;
            i++;

            if (interactive) {
                System.out.println("[Press any key]");
                KB.nextLine();
            }

            String indent1 = incIndent(indent);
            EAAsyncSystem sys1 = get.left;
            if (debug) {
                System.out.println(indent1 + "(" + bounds.state + ")\n" + sys1.toString(indent1));
                System.out.println(indent1 + "Reduced one step by:");
                System.out.println(get.mid.toString(indent1 + "  "));  // !!!
                if (get.right != null) {  // XXX TODO null
                    System.out.println(indent1 + "Delta stepped by:");
                    System.out.println(get.right.toString(indent1 + "  "));  // !!!
                }
            }
            Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> run =
                    typeAndRunDAux(sys1, depth + 1, debug, incIndent(indent), bounds, terminals, interactive, gamma);
            if (run.isLeft()) {
                return run;
            } else {
                Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>> right = run.getRight();
                depthPruned.addAll(right.left);
                terminals1.addAll(right.right);
            }
        }

        for (Pair<EAEAPName, Map<EAPid, Pair<Role, EAIota>>> init : inits) {
            System.out.print("\n" + indent + "(" + stmp + "-" + i + ") ");
            System.out.println("Stepping " + init);
            Either<Exception, Triple<EAAsyncSystem, Tree<String>, Tree<String>>> step = sys.init(init);

            // TODO factor out below with above
            if (step.isLeft()) {
                throw new RuntimeException(step.getLeft());
            }
            Triple<EAAsyncSystem, Tree<String>, Tree<String>> get = step.getRight();
            bounds.state++;
            i++;

            if (interactive) {
                System.out.println("[Press any key]");
                KB.nextLine();
            }

            String indent1 = incIndent(indent);
            EAAsyncSystem sys1 = get.left;
            if (debug) {
                System.out.println(indent1 + "(" + bounds.state + ")\n" + sys1.toString(indent1));
                System.out.println(indent1 + "Reduced one step by:");
                System.out.println(get.mid.toString(indent1 + "  "));  // !!!
                if (get.right != null) {  // XXX TODO null
                    System.out.println(indent1 + "Delta stepped by:");
                    System.out.println(get.right.toString(indent1 + "  "));  // !!!
                }
            }
            Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> run =
                    typeAndRunDAux(sys1, depth + 1, debug, incIndent(indent), bounds, terminals, interactive, gamma);
            if (run.isLeft()) {
                return run;
            } else {
                Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>> right = run.getRight();
                depthPruned.addAll(right.left);
                terminals1.addAll(right.right);
            }
        }

        return Either.right(Pair.of(depthPruned, terminals1));
    }

    public static String incIndent(String m) {
        return m.isEmpty() ? ".   " : m + ".   ";
    }

    /* parsing */

    public static void testParser() {
        EATermFactory pf = EATermFactory.factory;
        EARuntimeFactory rf = EARuntimeFactory.factory;
        EATypeFactory tf = EATypeFactory.factory;

        //String input = "(A ! a((())))";
        String input = "let x: 1 <= A ! a((())) in suspend "
                + "(handler A {b(x: 1): A?{b(1).C!{c(1).end}} -> return (), c(y: 1): end -> return ()})";
        EATerm res = parseM(input);
        System.out.println("bbb: " + res);
    }

    public static EAComp parseM(String input) {
        Lexer lex = new EACalculusLexer(new ANTLRStringStream(input));
        EACalculusParser par = new EACalculusParser(new CommonTokenStream(lex));
        try {
            //par.setTreeAdaptor(new EATreeAdaptor());  // XXX this requires nodes to be CommonTree to add children -- adaptor only constructs each node individualy without children
            CommonTree tree = (CommonTree) par.start().getTree();
            //System.out.println("aaa: " + tree.getClass() + "\n" + tree.getText() + " ,, " + tree.getChild(0) + " ,, " + tree.getChild(1));

            EAComp res = new EAFuncNamesFixer().parse(new EAASTBuilder().visitM((CommonTree) tree.getChild(0)));
            return res;

            //tree.token;
        } catch (RecognitionException x) {
            throw new RuntimeException(x);
        }
    }

    public static EAVType parseA(String input) {
        Lexer lex = new EACalculusLexer(new ANTLRStringStream(input));
        EACalculusParser par = new EACalculusParser(new CommonTokenStream(lex));
        try {
            CommonTree tree = (CommonTree) par.type().getTree();
            return new EAASTBuilder().visitA(tree);
        } catch (RecognitionException x) {
            throw new RuntimeException(x);
        }
    }

    public static EAExpr parseV(String input) {
        Lexer lex = new EACalculusLexer(new ANTLRStringStream(input));
        EACalculusParser par = new EACalculusParser(new CommonTokenStream(lex));
        try {
            CommonTree tree = (CommonTree) par.nV().getTree();
            return new EAFuncNamesFixer().parse(new EAASTBuilder().visitV(tree));
        } catch (RecognitionException x) {
            throw new RuntimeException(x);
        }
    }

    public static EALType parseSessionType(String input) {
        Lexer lex = new EACalculusLexer(new ANTLRStringStream(input));
        EACalculusParser par = new EACalculusParser(new CommonTokenStream(lex));
        try {
            CommonTree tree = (CommonTree) par.session_type().getTree();
            return new EAASTBuilder().visitSessionType(tree);
        } catch (RecognitionException x) {
            throw new RuntimeException(x);
        }
    }


	/*public static class EATreeAdaptor extends CommonTreeAdaptor {
		static EAPFactory pf = EAPFactory.factory;
		static EAPRuntimeFactory rf = EAPRuntimeFactory.factory;
		static EATypeFactory tf = EATypeFactory.factory;

		public EATreeAdaptor() {
		}

		// Generated parser seems to use nil to create "blank" nodes and then "fill them in"
		//@Override public Object nil() {return new ScribNil();}

		// Create a Tree (ScribNode) from a Token
		// N.B. not using AstFactory, construction here is pre adding children (and also here directly record parsed Token, not recreate)
		@Override public EAPVal create(Token t) {
			switch (t.getText()) {
				case "RETURN": {
						pf.returnn()
				}
			}
		}
	}*/

    /* ... */

    public static void typeCheckSystemOld(EASystem sys) {
        typeCheckSystemOld(sys, false);
    }

    public static void typeCheckSystemOld(EASystem sys, boolean debug) {
        if (debug) {
            System.out.println("Type checking system:");
        }
        Either<Exception, List<Tree<String>>> t = sys.type();
        if (t.isLeft()) {
            throw new RuntimeException(t.getLeft());
        }
        if (debug) {
            System.out.println(t.getRight().stream()
                    .map(x -> x.toString("  ")).collect(Collectors.joining("\n\n")));
        }
    }

    public static void typeAndRunOld(EASystem sys, int steps) {
        typeAndRunOld(sys, steps, false);
    }

    // steps -1 for unbounded
    public static void typeAndRunOld(EASystem sys, int steps, boolean debug) {
        System.out.println("\nInitial system:\n" + sys);
        typeCheckSystemOld(sys, debug);

        int rem = steps;
        Map<EAPid, Set<EAPid>> pids = sys.canStep();
        for (; !pids.isEmpty() && rem != 0; rem--) {
            //sys = sys.reduce(pids.keySet().iterator().next());  // FIXME HERE HERE always first act  // keyset is can-step-pids, (currently unused) Set is "partners"
            Pair<EASystem, Tree<String>> reduce = sys.reduce(pids.keySet().iterator().next());
            sys = reduce.left;
            if (debug) {
                System.out.println("\n" + sys);
                System.out.println("\nReduced one step by:");
                System.out.println(reduce.right.toString("  "));
            }
            typeCheckSystemOld(sys, debug);
            pids = sys.canStep();
        }

        if (!debug) {
            System.out.println();
            System.out.println("Result steps(" + steps + "):");
            System.out.println(sys);
        }

        if (steps == -1) {
            if (sys.actors.values().stream().anyMatch(x -> !x.T.isIdle() || !x.sigma.isEmpty())) {
                throw new RuntimeException("Stuck: " + sys);
            }
        } else if (rem != 0) {
            throw new RuntimeException("Stuck rem=" + rem + ": " + sys);
        }
    }
}
