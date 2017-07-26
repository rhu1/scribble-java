package org.scribble.ext.assrt.core.model.global;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.scribble.ext.assrt.core.ast.global.AssrtCoreGProtocolDeclTranslator;
import org.scribble.ext.assrt.model.endpoint.AssrtEAccept;
import org.scribble.ext.assrt.model.endpoint.AssrtEAction;
import org.scribble.ext.assrt.model.endpoint.AssrtEConnect;
import org.scribble.ext.assrt.model.endpoint.AssrtEReceive;
import org.scribble.ext.assrt.model.endpoint.AssrtESend;
import org.scribble.ext.assrt.model.global.actions.AssrtSSend;
import org.scribble.ext.assrt.parser.assertions.formula.AssrtFormulaFactory;
import org.scribble.ext.assrt.sesstype.formula.AssrtBoolFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtTrueFormula;
import org.scribble.ext.assrt.sesstype.name.AssrtAnnotDataType;
import org.scribble.ext.assrt.sesstype.name.AssrtDataTypeVar;
import org.scribble.ext.assrt.util.JavaSmtWrapper;
import org.scribble.main.Job;
import org.scribble.model.MPrettyState;
import org.scribble.model.MState;
import org.scribble.model.endpoint.EState;
import org.scribble.model.endpoint.EStateKind;
import org.scribble.model.endpoint.actions.EAction;
import org.scribble.model.endpoint.actions.EReceive;
import org.scribble.model.global.SModelFactory;
import org.scribble.model.global.actions.SAction;
import org.scribble.sesstype.Payload;
import org.scribble.sesstype.kind.Global;
import org.scribble.sesstype.name.Op;
import org.scribble.sesstype.name.PayloadElemType;
import org.scribble.sesstype.name.Role;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class AssrtCoreSState extends MPrettyState<Void, SAction, AssrtCoreSState, Global>
{
	private final Set<Role> subjs = new HashSet<>();  // Hacky: mostly because EState has no self -- for progress checking
	
	// Cf. SState.config
	private final Map<Role, EState> P;
	private final Map<Role, Map<Role, AssrtESend>> Q;  // null value means connected and empty -- dest -> src -> msg
	
	/*private final Map<Role, Map<Role, PayloadVar>> ports;  // Server -> Client -> port
	private final Map<Role, Set<PayloadVar>> owned;*/
	
	// Cf. history sensitivity
	private final Map<Role, Set<AssrtDataTypeVar>> K;  // "Knowledge" of annotation vars (payloads and recursions)
			// FIXME: for now, assume globally distinct annot vars?  but conflicts with unfolding recursion annot vars?
			// Currently assuming unique annot var declarations -- otherwise need to consider, e.g., A->B(x).C->B(x)
					// N.B. unique vars checked syntactically -- not being checked in model, which would fail on recursion cycles (e.g., mu X.A->B(x:Int).X)
			// CHECKME: should this info really be part of the model states?  or just collected by analysis on top?
					// Being in the state causes "implicit unrolling" for recursions, before/after "known" state
			// "Knowledge" not the best term? -- K+F represents per role "commitments"?
	
	// Cf. temporal satisfiability?
	private final Set<AssrtBoolFormula> F;  // FIXME: shouldn't be part of state?  i.e., shouldn't be used to ("syntactically") distinguish states?

	public AssrtCoreSState(Map<Role, EState> P, boolean explicit)
	{
		this(P, makeQ(P.keySet(), explicit),
				makeK(P.keySet()),
				//new HashMap<>());
				new HashSet<>());
	}

	// Pre: non-aliased "ownership" of all Map contents
	protected AssrtCoreSState(Map<Role, EState> P, Map<Role, Map<Role, AssrtESend>> Q,
			Map<Role, Set<AssrtDataTypeVar>> K, Set<AssrtBoolFormula> F)//Map<AssrtDataTypeVar, AssrtBoolFormula> F)
	{
		super(Collections.emptySet());
		this.P = Collections.unmodifiableMap(P);
		this.Q = Collections.unmodifiableMap(Q);  // Don't need copyQ, etc. -- should already be fully "owned"
		this.K = Collections.unmodifiableMap(K);
		//this.F = Collections.unmodifiableMap(F);
		this.F = Collections.unmodifiableSet(F);
	}

	public boolean isReceptionError()
	{
		return this.P.entrySet().stream().anyMatch(e ->  // e: Entry<Role, EState>
				{
					EState s = e.getValue();
					EStateKind k = s.getStateKind();
					if (k != EStateKind.UNARY_INPUT && k != EStateKind.POLY_INPUT)
					{
						return false;
					}
					Role dest = e.getKey();
					List<EAction> as = s.getActions();
					Role src = as.get(0).peer;
					return hasMessage(dest, src) && !as.contains(this.Q.get(dest).get(src).toDual(src));
				}
		);
	}

	public boolean isUnfinishedRoleError(Map<Role, EState> E0)
	{
		return this.isTerminal() &&
				this.P.entrySet().stream().anyMatch(e -> isActive(e.getValue(), E0.get(e.getKey()).id));
	}

	public boolean isOrphanError(Map<Role, EState> E0)
	{
		/*return this.P.entrySet().stream().anyMatch((e) -> isInactive(e.getValue(), E0.get(e.getKey()).id)
				&& (this.P.keySet().stream().anyMatch((r) -> hasMessage(e.getKey(), r))));*/
		return this.P.entrySet().stream().anyMatch(e ->
				   isInactive(e.getValue(), E0.get(e.getKey()).id)
				&& (this.P.keySet().stream().anyMatch(r -> hasMessage(e.getKey(), r))
						//|| !this.owned.get(e.getKey()).isEmpty()  
						
								// FIXME: need AnnotEConnect to consume owned properly

				));
	}
	
	public boolean isUnknownDataTypeVarError()
	{
		return this.P.entrySet().stream().anyMatch(e ->
				e.getValue().getAllActions().stream().anyMatch(a -> 
				{
					if (a instanceof AssrtESend)
					{
						Set<AssrtDataTypeVar> tmp = new HashSet<>(this.K.get(e.getKey()));
						((AssrtESend) a).payload.elems.forEach(pe ->  // Currently exactly one elem
						{
							if (pe instanceof AssrtAnnotDataType)
							{
								tmp.add(((AssrtAnnotDataType) pe).var);
							}
							else
							{
								System.err.println("[assrt-core] Shouldn't get in here: " + pe);  // FIXME
							}
						});
						return ((AssrtESend) a).ass.getVars().stream().anyMatch(v -> !tmp.contains(v));
					}
					else
					{
						// FIXME: receive assertions
					}
					return false;
				}));
	}
	
	// i.e., has an action with an unsatisfiable assertion given existing assertions
	public boolean isUnsatisfiableError(Job job)
	{
		return this.P.entrySet().stream().anyMatch(e ->
				e.getValue().getAllActions().stream().anyMatch(a -> 
				{
					if (a instanceof AssrtESend)
					{
						JavaSmtWrapper jsmt = JavaSmtWrapper.getInstance();
						AssrtBoolFormula ass = ((AssrtESend) a).ass;
						if (ass.equals(AssrtTrueFormula.TRUE))
						{
							return false;
						}

						Set<IntegerFormula> varsF = this.F.stream().flatMap(f -> f.getVars().stream()
								.map(v -> jsmt.ifm.makeVariable(v.toString()))).collect(Collectors.toSet());
						/*Set<IntegerFormula> varsA = ass.getVars().stream()
								.map(v -> jsmt.ifm.makeVariable(v.toString())).collect(Collectors.toSet());
						varsA.removeAll(varsF);*/  // No: the only difference should be single action pay var, and always want to exists quantify it (not only if not F, e.g., recursion)
						Set<IntegerFormula> varsA = new HashSet<>();
						varsA.add(jsmt.ifm.makeVariable(((AssrtAnnotDataType) a.payload.elems.get(0)).var.toString()));  
								// Adding even if var not used
								// N.B. includes the case for recursion cycles where var is "already" in F

						AssrtBoolFormula tmp = this.F.stream().reduce(
								AssrtTrueFormula.TRUE,
								(b1, b2) -> AssrtFormulaFactory.BinBoolFormula("&&", b1, b2));  // F emptyset at start
						BooleanFormula PP = tmp.getJavaSmtFormula();
						BooleanFormula AA = ass.getJavaSmtFormula();
						if (!varsA.isEmpty())  // FIXME: now never empty
						{
							AA = jsmt.qfm.exists(new LinkedList<>(varsA), AA);
						}
						BooleanFormula impli = jsmt.bfm.implication(PP, AA);
						if (!varsF.isEmpty())
						{
							impli = jsmt.qfm.forall(new LinkedList<>(varsF), impli);
						}
						
						job.debugPrintln("\n[assrt-core] Checking satisfiability for " + e.getKey() + " at " + e.getValue() + ": " + impli);
							
						if (!jsmt.isSat(impli))
						{
							return true;
						}
					}
					else
					{
						// FIXME: receive assertions
					}
					return false;
				}));
	}

	public boolean isConnectionError()
	{
		return this.P.entrySet().stream().anyMatch(e -> 
			e.getValue().getActions().stream().anyMatch(a ->
				(a.isConnect() || a.isAccept()) && isConnected(e.getKey(), a.peer) 

						// FIXME: check for pending port, if so then port is used -- need to extend an AnnotEConnect type with ScribAnnot (cf. AnnotPayloadType)

		));
	}

	public boolean isUnconnectedError()
	{
		return this.P.entrySet().stream().anyMatch(e -> 
			e.getValue().getActions().stream().anyMatch(a ->
				(a.isSend() || a.isReceive()) && !isConnected(e.getKey(), a.peer)
		));
	}

	public boolean isSynchronisationError()
	{
		return this.P.entrySet().stream().anyMatch(e ->  // e: Entry<Role, EState>
				{
					EState s = e.getValue();
					EStateKind k = s.getStateKind();
					if (k != EStateKind.ACCEPT)
					{
						return false;
					}
					Role dest = e.getKey();
					List<EAction> as = s.getActions();
					Role src = as.get(0).peer;
					return //hasMessage(dest, src)  // FIXME: hasMessage for pending connection message
							isPendingConnection(src, dest)
							&& !as.contains(((AssrtCoreEPendingConnection) this.Q.get(dest).get(src)).getMessage().toDual(src));
				}
		);
	}

	/*public boolean isDisconnectedError()
	{
		return this.P.entrySet().stream().anyMatch((e) -> 
			e.getValue().getActions().stream().anyMatch((a) ->
				a.isDisconnect() && this.Q.get(e.getKey()).get(a.peer) != null
		));
	}
	
	// Error of opening a port when already connected or another port is still open
	public boolean isPortOpenError()
	{
		for (Entry<Role, EState> e : this.P.entrySet())
		{
			for (EAction a : e.getValue().getActions())
			{
				if (a.isSend())
				{
					for (PayloadType<?> pt : (Iterable<PayloadType<?>>) a.payload.elems.stream()
							.filter(x -> x instanceof AnnotType)::iterator)
					{
						if (pt instanceof AnnotPayloadType<?>)
						{
							// FIXME: factor out annot parsing
							AnnotPayloadType<?> apt = (AnnotPayloadType<?>) pt;
							String annot = ((AnnotString) apt.annot).val;
							String key = annot.substring(0, annot.indexOf("="));
							String val = annot.substring(annot.indexOf("=")+1,annot.length());
							if (key.equals("open"))
							{
								Role portRole = new Role(val);
								// FIXME: generalise
								if (isConnected(e.getKey(), portRole) || isPendingConnected(e.getKey(), portRole))
								{
									return true;
								}
							}
							else
							{
								throw new RuntimeException("[f17] TODO: " + a);
							}
						}
						else if (pt instanceof PayloadVar)
						{
							
						}
						else
						{
							throw new RuntimeException("[f17] TODO: " + a);
						}
					}
				}
			}
		}
		return false;
	}

	// Error of trying to send a PayloadVar that is not "owned" by the sender
	public boolean isPortOwnershipError()
	{
		for (Entry<Role, EState> e : this.P.entrySet())
		{
			for (EAction a : e.getValue().getActions())
			{
				if (a.isSend())
				{
					for (PayloadType<?> pt : (Iterable<PayloadType<?>>) a.payload.elems.stream()
							.filter(x -> x instanceof AnnotType)::iterator)
					{
						if (pt instanceof AnnotPayloadType<?>)
						{
							
						}
						else if (pt instanceof PayloadVar)
						{
							if (!this.owned.get(e.getKey()).contains((PayloadVar) pt))
							{
								return true;
							}
						}
						else
						{
							throw new RuntimeException("[f17] TODO: " + a);
						}
					}
				}
			}
		}
		return false;
	}*/
	
	public Map<Role, List<EAction>> getFireable()
	{
		Map<Role, List<EAction>> res = new HashMap<>();
		for (Entry<Role, EState> e : this.P.entrySet())
		{
			Role self = e.getKey();
			EState s = e.getValue();
			res.put(self, new LinkedList<>());
			for (EAction a : s.getActions())
			{
				if (a.isSend())
				{
					AssrtESend es = (AssrtESend) a;
					getSendFireable(res, self, es);
				}
				else if (a.isReceive())
				{
					AssrtEReceive er = (AssrtEReceive) a;
					getReceiveFireable(res, self, er);
				}
				else if (a.isConnect())
				{
					AssrtEConnect ec = (AssrtEConnect) a;
					getConnectFireable(res, self, ec);
				}
				else if (a.isAccept())
				{
					AssrtEAccept ea = (AssrtEAccept) a;
					getAcceptFireable(res, self, ea);
				}
				/*else if (a.isDisconnect())
				{
					EDisconnect ld = (EDisconnect) a;
					getDisconnectFireable(res, self, ld);
				}*/
				else
				{
					throw new RuntimeException("[assrt-core] Shouldn't get in here: " + a);
				}
			}
		}
		return res;
	}

	private void getSendFireable(Map<Role, List<EAction>> res, Role self, AssrtESend es)
	{
		if (hasPendingConnect(self) || !isConnected(self, es.peer) || hasMessage(es.peer, self))
		{
			return;
		}

		// Check assertion?
		//boolean ok = JavaSmtWrapper.getInstance().isSat(es.assertion.getFormula(), context);
	
		//...can only send if true? (by API gen assertion failure means definitely not sending it) -- unsat as bad terminal state (safety error)?  no: won't catch all assert errors (branches)
		// check assertion satisfiable?  i.e., satisfiability part of operational semantics for model construction? or just record constraints and check later?
		// -- current assertions *imply* additional ones?
				
		// Or: assertion error as special queue token? for error preservation -- Cf. "decoupled" request/accept
		
		boolean ok = true;
		/*for (PayloadElemType<?> pt : (Iterable<PayloadElemType<?>>) 
				es.payload.elems.stream().filter(x -> x instanceof AssrtPayloadElemType<?>)::iterator)*/
		PayloadElemType<?> pt = es.payload.elems.get(0);  // assrt-core is hardcoded to one payload elem (empty source payload is filled in)
		{
			if (pt instanceof AssrtAnnotDataType)
			{
				// OK -- currently not checking K-bound assertion vars (cf. isUnknownVarError) -- nor satisfiability (send ass implies receive ss)
				// FIXME: currently fire requires send and receive assertions (and both hacked to True) to be syntactically equal, which is wrong
			}
			else
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + pt);  // "Encode" pay elem vars by fresh annot data elems for now
			}
		}
		if (ok)
		{	
			res.get(self).add(es);
		}
	}

	private void getReceiveFireable(Map<Role, List<EAction>> res, Role self, EReceive er)
	{
		if (hasPendingConnect(self) || !hasMessage(self, er.peer))
		{
			return;
		}

		AssrtESend m = this.Q.get(self).get(er.peer);
		if (er.toDual(self).equals(m))  //&& !(m instanceof F17EBot)
		{
			res.get(self).add(er);
		}
	}

	private void getConnectFireable(Map<Role, List<EAction>> res, Role self, AssrtEConnect es)
	{
		if (hasPendingConnect(self) ||
				   // not ( Q(r, r') = Q(r', r) = \bot ) -- i.e., either of them are not \bot
				   isConnected(self, es.peer) || isConnected(es.peer, self)
				|| isPendingConnection(es.peer, self))  // self input queue from es.peer is <a>
						// isPendingConnection(self, es.peer) subsumed by hasPendingConnect(self)
		{
			return;
		}
		
		// FIXME: factor out with send?
		boolean ok = true;
		PayloadElemType<?> pt = es.payload.elems.get(0);  // assrt-core is hardcoded to one payload elem (empty source payload is filled in)
		{
			if (pt instanceof AssrtAnnotDataType)
			{
				// OK -- currently not checking K-bound assertion vars (cf. isUnknownVarError) -- nor satisfiability (send ass implies receive ss)
				// FIXME: currently fire requires send and receive assertions (and both hacked to True) to be syntactically equal, which is wrong
			}
			else
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + pt);  // "Encode" pay elem vars by fresh annot data elems for now
			}
		}
		if (ok)
		{	
			res.get(self).add(es);
		}
		
		// FIXME: open/port annotations

			/*EState plt = this.P.get(lo.peer);
			if (plt.getActions().contains(lo.toDual(self)))
			{

				boolean ok = true;
				for (PayloadType<?> pt : (Iterable<PayloadType<?>>) a.payload.elems.stream()
						.filter((x) -> x instanceof AnnotType)::iterator)
				{
					if (pt instanceof AnnotPayloadType<?>)
					{
						AnnotPayloadType<?> apt = (AnnotPayloadType<?>) pt;
						String annot = ((AnnotString) apt.annot).val;
						String key = annot.substring(0, annot.indexOf("="));
						String val = annot.substring(annot.indexOf("=")+1,annot.length());
						if (key.equals("port"))
						{
							Role portRole = new Role(val);
							if (isConnected(self, portRole) || isPendingConnected(self, portRole))
							{
								ok = false;
								break;
							}
							if (!val.equals(lo.peer.toString()))
							{
								ok = false;
								break;
							}
						}
						else  // TODO: connect-with-message could also be open-annot
						{
							throw new RuntimeException("[f17] TODO: " + a);
						}
					}
					else if (pt instanceof PayloadVar)  // Check linear ownership of port
					{
						if (!this.owned.get(self).contains(pt) || !pt.equals(this.ports.get(lo.peer).get(self)))
						{
							ok = false;
							break;
						}
					}
					else
					{
						throw new RuntimeException("[f17] TODO: " + a);
					}
				}
				if (ok)
				{	
					res.get(self).add(lo);
				}

			}*/
	}

	// Based on getReceiveFireable
	private void getAcceptFireable(Map<Role, List<EAction>> res, Role self, AssrtEAccept ea)
	{
		if (hasPendingConnect(self) || !isPendingConnection(ea.peer, self))
		{
			return;
		}

		AssrtEConnect ec = ((AssrtCoreEPendingConnection) this.Q.get(self).get(ea.peer)).getMessage();
		if (ea.toDual(self).equals(ec))
		{
			res.get(self).add(ea);
		}
	}

	/*private void getDisconnectFireable(Map<Role, List<EAction>> res, Role self, EDisconnect ld)
	{
		if (!(this.Q.get(self).get(ld.peer) instanceof F17EBot)  // FIXME: isConnected
				&& this.Q.get(self).get(ld.peer) == null)
		{
			res.get(self).add(ld);
		}
	}*/
	
	// Pre: getFireable().get(self).contains(a)
	public AssrtCoreSState fire(Role self, EAction a)  // Deterministic
	{
		Map<Role, EState> P = new HashMap<>(this.P);
		Map<Role, Map<Role, AssrtESend>> Q = AssrtCoreSState.copyQ(this.Q);
		Map<Role, Set<AssrtDataTypeVar>> K = copyK(this.K);
		//Map<AssrtDataTypeVar, AssrtBoolFormula> F = new HashMap<>(this.F);
		Set<AssrtBoolFormula> F = new HashSet<>(this.F);
		EState succ = P.get(self).getSuccessor(a);

		if (a.isSend())
		{
			fireSend(P, Q, K, F, self, (AssrtESend) a, succ);
		}
		else if (a.isReceive())
		{
			fireReceive(P, Q, K, self, (EReceive) a, succ);
		}
		else if (a.isConnect())
		{
			fireRequest(P, Q, K, F, self, (AssrtEConnect) a, succ);
		}
		else if (a.isAccept())
		{
			fireAccept(P, Q, K, self, (AssrtEAccept) a, succ);
		}
		/*else if (a.isDisconnect())
		{
			EDisconnect ld = (EDisconnect) a;
			P.put(self, succ);
			Q.get(self).put(ld.peer, BOT);
		}*/
		else
		{
			throw new RuntimeException("[assrt-core] Shouldn't get in here: " + a);
		}
		return new AssrtCoreSState(P, Q, K, F);
	}

	// Update (in place) P, Q, K and F
	private static void fireSend(Map<Role, EState> P, Map<Role, Map<Role, AssrtESend>> Q,
			Map<Role, Set<AssrtDataTypeVar>> K, Set<AssrtBoolFormula> F,
			Role self, AssrtESend es, EState succ)
	{
		P.put(self, succ);
		Q.get(es.peer).put(self, es);
		outputUpdateKF(K, F, self, es);
	}

	private static void fireReceive(Map<Role, EState> P, Map<Role, Map<Role, AssrtESend>> Q,
			Map<Role, Set<AssrtDataTypeVar>> K,   // FIXME: manage F with receive assertions?
			Role self, EReceive er, EState succ)
	{
		P.put(self, succ);
		Q.get(self).put(er.peer, null);  // null is \epsilon
		inputUpdateK(K, self, er);
	}

	private static void fireRequest(Map<Role, EState> P, Map<Role, Map<Role, AssrtESend>> Q,
			Map<Role, Set<AssrtDataTypeVar>> K, Set<AssrtBoolFormula> F,
			Role self, AssrtEConnect es, EState succ)
	{
		P.put(self, succ);
		Q.get(es.peer).put(self, new AssrtCoreEPendingConnection(es));
		outputUpdateKF(K, F, self, es);
	}

	private static void fireAccept(Map<Role, EState> P, Map<Role, Map<Role, AssrtESend>> Q,
			Map<Role, Set<AssrtDataTypeVar>> K, //Set<AssrtBoolFormula> F,
			Role self, AssrtEAccept ea, EState succ)
	{
		P.put(self, succ);
		Q.get(self).put(ea.peer, null);
		Q.get(ea.peer).put(self, null);
		inputUpdateK(K, self, ea);
	}

	private static void outputUpdateKF(Map<Role, Set<AssrtDataTypeVar>> K, Set<AssrtBoolFormula> F, Role self, EAction o)  // FIXME: EAction closest base type
	{
		/*for (PayloadElemType<?> pt : (Iterable<PayloadElemType<?>>) 
					(a.payload.elems.stream().filter(x -> x instanceof AssrtPayloadElemType<?>))::iterator)*/
		PayloadElemType<?> pt = o.payload.elems.get(0);
		{
			if (pt instanceof AssrtAnnotDataType)
			{
				// Update K
				AssrtDataTypeVar v = ((AssrtAnnotDataType) pt).var;
				putK(K, self, v);
				
				//...record assertions so far -- later error checking: *for all* values that satisify those, it should imply the next assertion
				//putF(F, v, es.bf);
				putF(F, ((AssrtEAction) o).getAssertion());  // Recorded "globally" -- cf. async K updates
			}
			else
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + o);  
						// Regular DataType pay elems have been given fresh annot vars (AssrtCoreGProtocolDeclTranslator.parsePayload) -- no other pay elems allowed
			}
		}
	}

  // No F update: F already done "globally" on send
	private static void inputUpdateK(Map<Role, Set<AssrtDataTypeVar>> K, Role self, EAction i)  // FIXME: EAction closest base type
	{
		/*for (PayloadElemType<?> pt : (Iterable<PayloadElemType<?>>) 
					(a.payload.elems.stream().filter(x -> x instanceof AssrtPayloadElemType<?>))::iterator)*/
		PayloadElemType<?> pt = i.payload.elems.get(0);
		{
			if (pt instanceof AssrtAnnotDataType)
			{
				// Update K
				AssrtDataTypeVar v = ((AssrtAnnotDataType) pt).var;
				putK(K, self, v);

				//putF(F, es.bf);  // No F update: F already done "globally" on send
			}
			else
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + i);  
						// Regular DataType pay elems have been given fresh annot vars (AssrtCoreGProtocolDeclTranslator.parsePayload) -- no other pay elems allowed
			}
		}
	}

	private boolean hasMessage(Role self, Role peer)
	{
		return isConnected(peer, self)              // input queue is established (not \bot and not <a>)
				&& this.Q.get(self).get(peer) != null;  // input queue is not empty
	}
	
	// Direction sensitive (not symmetric) -- isConnected means dest has established input queue from src
	// i.e. "fully" established, not "pending" -- semantics relies on all action firing being guarded on !hasPendingConnect
	private boolean isConnected(Role dest, Role src)  // N.B. is more like the "input buffer" at r1 for r2 -- not the actual "connection from r1 to r2"
	{
		AssrtESend es = this.Q.get(dest).get(src);
		return !(es instanceof AssrtCoreEBot) && !(es instanceof AssrtCoreEPendingConnection);
		//return es != null && es.equals(AssrtCoreEBot.ASSSRTCORE_BOT);  // Would be same as above
	}

	// req waiting for acc -- cf. reverse direction to isConnect
	private boolean isPendingConnection(Role req, Role acc)  // FIXME: for open/port annotations
	{
		//return (this.ports.get(r1).get(r2) != null) || (this.ports.get(r2).get(r1) != null);
		AssrtESend es = this.Q.get(acc).get(req);  // N.B. reverse direction to isConnected
		return es instanceof AssrtCoreEPendingConnection;
	}

  // FIXME: rename hasPendingRequest
	private boolean hasPendingConnect(Role req)
	{
		return this.Q.keySet().stream().anyMatch(acc -> isPendingConnection(req, acc));
	}

	public Map<Role, EState> getP()
	{
		return this.P;
	}
	
	public Map<Role, Map<Role, AssrtESend>> getQ()
	{
		return this.Q;
	}
	
	public Set<Role> getSubjects()
	{
		return Collections.unmodifiableSet(this.subjs);
	}
	
	public void addSubject(Role subj)
	{
		this.subjs.add(subj);
	}
	
	@Override
	protected String getNodeLabel()
	{
		String lab = "(P=" + this.P + ", Q=" + this.Q + ", K=" + this.K + ", F=" + this.F + ")";
		//return "label=\"" + this.id + ":" + lab.substring(1, lab.length() - 1) + "\"";
		return "label=\"" + this.id + ":" + lab + "\"";
	}

	@Override
	public void addEdge(SAction a, AssrtCoreSState s)  // Visibility hack (for AssrtCoreSModelBuilder::build)
	{
		super.addEdge(a, s);
	}
	
	@Override
	public final int hashCode()
	{
		int hash = 79;
		hash = 31 * hash + this.P.hashCode();
		hash = 31 * hash + this.Q.hashCode();
		hash = 31 * hash + this.K.hashCode();
		hash = 31 * hash + this.F.hashCode();
		return hash;
	}

	// Not using id, cf. ModelState -- FIXME? use a factory pattern that associates unique states and ids? -- use id for hash, and make a separate "semantic equals"
	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof AssrtCoreSState))
		{
			return false;
		}
		AssrtCoreSState them = (AssrtCoreSState) o;
		return them.canEquals(this) && this.P.equals(them.P) && this.Q.equals(them.Q)
				&& this.K.equals(them.K) && this.F.equals(them.F);
	}

	@Override
	protected boolean canEquals(MState<?, ?, ?, ?> s)
	{
		return s instanceof AssrtCoreSState;
	}
	
	// isActive(SState, Role) becomes isActive(EState)
	public static boolean isActive(EState s, int init)
	{
		return !isInactive(s, init);
	}
	
	private static boolean isInactive(EState s, int init)
	{
		//return s.isTerminal() || (s.id == init && s.getStateKind() == EStateKind.ACCEPT);
		return s.isTerminal();
				// s.isTerminal means non-empty actions (i.e., edges) -- i.e., non-end (cf., fireable)
	}
	
	
	// FIXME: factor out into own classes
	
	private static Map<Role, Map<Role, AssrtESend>> makeQ(Set<Role> rs, boolean explicit)
	{
		AssrtESend init = explicit ? AssrtCoreEBot.ASSSRTCORE_BOT : null;
		Map<Role, Map<Role, AssrtESend>> res = new HashMap<>();
		for (Role r1 : rs)
		{
			HashMap<Role, AssrtESend> tmp = new HashMap<>();
			for (Role r2 : rs)
			{
				if (!r2.equals(r1))
				{
					tmp.put(r2, init);
				}
			}
			res.put(r1, tmp);
		}
		return res;
	}
	
	private static Map<Role, Map<Role, AssrtESend>> copyQ(Map<Role, Map<Role, AssrtESend>> Q)
	{
		Map<Role, Map<Role, AssrtESend>> copy = new HashMap<>();
		for (Role r : Q.keySet())
		{
			copy.put(r, new HashMap<>(Q.get(r)));
		}
		return copy;
	}

	private static Map<Role, Set<AssrtDataTypeVar>> makeK(Set<Role> rs)
	{
		return rs.stream().collect(Collectors.toMap(r -> r, r -> new HashSet<>()));
	}

	private static Map<Role, Set<AssrtDataTypeVar>> copyK(Map<Role, Set<AssrtDataTypeVar>> K)
	{
		return K.entrySet().stream().collect(Collectors.toMap(Entry::getKey, e -> new HashSet<>(e.getValue())));
	}
	
	private static void putK(Map<Role, Set<AssrtDataTypeVar>> K, Role r, AssrtDataTypeVar v)
	{
		Set<AssrtDataTypeVar> tmp = K.get(r);
		/*if (tmp == null)  // No: makeK already made all Sets -- cf. makeQ, and no putQ
		{
			tmp = new HashSet<>();
			K.put(r, tmp);
		}*/
		tmp.add(v);
	}

	private static void putF(Set<AssrtBoolFormula> F, AssrtBoolFormula f)
	{
		F.add(f);
	}
	
	/*private static Map<Role, Map<Role, PayloadVar>> copyPorts(Map<Role, Map<Role, PayloadVar>> ports)
	{
		Map<Role, Map<Role, PayloadVar>> copy = new HashMap<>();
		for (Role r : ports.keySet())
		{
			copy.put(r, new HashMap<>(ports.get(r)));
		}
		return copy;
	}

	private static Map<Role, Set<PayloadVar>> makeOwned(Set<Role> rs)
	{
		return rs.stream().collect(Collectors.toMap((r) -> r, (r) -> new HashSet<>()));
	}
	
	private static Map<Role, Set<PayloadVar>> copyOwned(Map<Role, Set<PayloadVar>> owned)
	{
		return owned.entrySet().stream().collect(Collectors.toMap((e) -> e.getKey(), (e) -> new HashSet<>(e.getValue())));
	}*/

	/* // No longer "synchronous" per se, just blocking for requestor
	public AssrtSConfig sync(Role r1, EAction a1, Role r2, EAction a2)
	{
		Map<Role, EState> P = new HashMap<>(this.P);
		Map<Role, Map<Role, AssrtESend>> Q = copyQ(this.Q);
		Map<Role, Map<Role, PayloadVar>> ports = copyPorts(this.ports);
		Map<Role, Set<PayloadVar>> owned = copyOwned(this.owned);
		EState succ1 = P.get(r1).getSuccessor(a1);
		EState succ2 = P.get(r2).getSuccessor(a2);

		if ((a1.isConnect() && a2.isAccept())
				|| (a1.isAccept() && a2.isConnect()))
		{
			P.put(r1, succ1);
			P.put(r2, succ2);
			Q.get(r1).put(r2, null);
			Q.get(r2).put(r1, null);

			Role cself = a1.isConnect() ? r1 : r2;
			Role cpeer = a1.isConnect() ? r2 : r1;
			EConnect ec = (EConnect) (a1.isConnect() ? a1 : a2);
			
			//if (...)  // FIXME: check if port pending, if so then correct port used -- need AnnotEConnect type -- cf., isConnectionError
			{
				ports.get(cpeer).put(cself, null); // HACK FIXME: incorrect without proper checks
				//owned.get(cself).clear();  // Hack doesn't work: will clear others' pending ports
			}
			
			for (PayloadElemType<?> pt : (Iterable<PayloadElemType<?>>) ec.payload.elems.stream()
					.filter((x) -> x instanceof AnnotType)::iterator)
			{
				if (pt instanceof AnnotPayloadType<?>)
				{
					AnnotPayloadType<?> apt = (AnnotPayloadType<?>) pt;
					String annot = ((AnnotString) apt.annot).val;
					String key = annot.substring(0, annot.indexOf("="));
					String val = annot.substring(annot.indexOf("=")+1,annot.length());
					if (key.equals("open"))  // Duplicated from fire/isSend -- opening+passing a port as part of connect
					{
						Role portRole = new Role(val);
						ports.get(cself).put(portRole, apt.var);
						owned.get(cpeer).add(apt.var);
					}
					else
					{
						throw new RuntimeException("[f17] TODO: " + ec);
					}
				}
				else if (pt instanceof PayloadVar)
				{
					PayloadVar pv = (PayloadVar) pt;
					owned.get(cself).remove(pv);
					owned.get(cpeer).add(pv);
				}
				else
				{
					throw new RuntimeException("[f17] TODO: " + ec);
				}
			}
		}
		else
		{
			throw new RuntimeException("[f17] Shouldn't get in here: " + a1 + ", " + a2);
		}
		return new AssrtCoreSState(P, Q, ports, owned);
	}*/
}


// \bot
class AssrtCoreEBot extends AssrtESend
{
	// N.B. must be initialised *before* ASSSRTCORE_BOT
	private static final Payload ASSRTCORE_EMPTY_PAYLOAD =
			new Payload(Arrays.asList(new AssrtAnnotDataType(new AssrtDataTypeVar("_BOT"), AssrtCoreGProtocolDeclTranslator.UNIT_DATATYPE)));
			// Cf. Payload.EMPTY_PAYLOAD

	public static final AssrtCoreEBot ASSSRTCORE_BOT = new AssrtCoreEBot();


	//public AssrtCoreEBot(EModelFactory ef)
	private AssrtCoreEBot()
	{
		super(null, Role.EMPTY_ROLE, Op.EMPTY_OPERATOR, ASSRTCORE_EMPTY_PAYLOAD, AssrtTrueFormula.TRUE);  // null ef OK?
	}
	
	@Override
	public boolean isSend()
	{
		return false;
	}
	
	@Override
	public AssrtEReceive toDual(Role self)
	{
		throw new RuntimeException("[assrt-core] Shouldn't get in here: " + this);
	}

	@Override
	public AssrtSSend toGlobal(SModelFactory sf, Role self)
	{
		throw new RuntimeException("[assrt-core] Shouldn't get in here: " + this);
	}
	
	@Override
	public String toString()
	{
		return "BOT";
	} 

	@Override
	public int hashCode()
	{
		int hash = 2273;
		hash = 31 * hash + super.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof AssrtCoreEBot))
		{
			return false;
		}
		return super.equals(obj);
	}
	
	@Override
	public boolean canEqual(Object o)  // FIXME: rename canEquals
	{
		return o instanceof AssrtCoreEBot;
	}
}

// <a>
class AssrtCoreEPendingConnection extends AssrtESend  // Q stores ESends (not EConnect)
{
	public static final Payload ASSRTCORE_EMPTY_PAYLOAD =
			new Payload(Arrays.asList(new AssrtAnnotDataType(new AssrtDataTypeVar("_BOT"), AssrtCoreGProtocolDeclTranslator.UNIT_DATATYPE)));
			// Cf. Payload.EMPTY_PAYLOAD
	
	private final AssrtEConnect msg;  // Not included in equals/hashCode

	//public AssrtCoreEPendingConnection(AssrtEModelFactory ef, Role r, MessageId<?> op, Payload pay, AssrtBoolFormula ass)
	public AssrtCoreEPendingConnection(AssrtEConnect msg)
	{
		super(null, msg.peer, msg.mid, msg.payload, msg.ass);  // HACK: null ef OK?  cannot access es.ef
		this.msg = msg;
	}
	
	public AssrtEConnect getMessage()
	{
		return this.msg;
	}
	
	@Override
	public boolean isSend()
	{
		return false;
	}
	
	@Override
	public AssrtEReceive toDual(Role self)
	{
		throw new RuntimeException("[assrt-core] Shouldn't get in here: " + this);
	}

	@Override
	public AssrtSSend toGlobal(SModelFactory sf, Role self)
	{
		throw new RuntimeException("[assrt-core] Shouldn't get in here: " + this);
	}
	
	@Override
	public String toString()
	{
		return "<" + super.toString() + ">";
	} 

	@Override
	public int hashCode()
	{
		int hash = 6091;
		hash = 31 * hash + super.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof AssrtCoreEPendingConnection))
		{
			return false;
		}
		return super.equals(obj);
	}
	
	@Override
	public boolean canEqual(Object o)  // FIXME: rename canEquals
	{
		return o instanceof AssrtCoreEPendingConnection;
	}
}