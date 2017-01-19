package org.scribble.ext.f17.ast.local;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.scribble.ext.f17.ast.F17AstFactory;
import org.scribble.ext.f17.ast.F17MessageAction;
import org.scribble.ext.f17.ast.global.F17GChoice;
import org.scribble.ext.f17.ast.global.F17GEnd;
import org.scribble.ext.f17.ast.global.F17GRec;
import org.scribble.ext.f17.ast.global.F17GRecVar;
import org.scribble.ext.f17.ast.global.F17GType;
import org.scribble.ext.f17.ast.global.action.F17GAction;
import org.scribble.ext.f17.ast.global.action.F17GConnect;
import org.scribble.ext.f17.ast.global.action.F17GDisconnect;
import org.scribble.ext.f17.ast.global.action.F17GMessageTransfer;
import org.scribble.ext.f17.ast.local.action.F17LAction;
import org.scribble.ext.f17.ast.local.action.F17LInput;
import org.scribble.ext.f17.main.F17Exception;
import org.scribble.ext.f17.main.F17SyntaxException;
import org.scribble.sesstype.name.RecVar;
import org.scribble.sesstype.name.Role;


// FIXME: factor out "original"/"extended" modes to CL interface
public class F17Projector
{
	private static final boolean EXTENDED = false;
	//private static final boolean EXTENDED = true;
	
	private final F17AstFactory factory = F17AstFactory.FACTORY;

	public F17Projector()
	{

	}

	public F17LType project(F17GType gt, Role r, Set<RecVar> delta) throws F17Exception
	{
		if (gt instanceof F17GChoice)
		{
			F17GChoice gc = (F17GChoice) gt;
			if (gc.cases.size() == 1)
			{
				Entry<F17GAction, F17GType> e = gc.cases.entrySet().iterator().next();
				F17GAction ga = e.getKey();
				if (ga.getRoles().contains(r))
				{
					Map<F17LAction, F17LType> gcases = new HashMap<>();
					gcases.put(project(ga, r), project(e.getValue(), r, Collections.emptySet()));
					return this.factory.LChoice(gcases);
				}
				else
				{
					return project(e.getValue(), r, delta);
				}
			}
			else // gc.cases.size() > 1
			{
				Map<F17LAction, F17LType> gCases = new HashMap<>();  // Guarded cases (J)
				Map<F17GAction, RecVar> rvCases = new HashMap<>();   // Unguarded rec vars
				Set<F17GAction> eCases = new HashSet<>();            // Unguraded end cases
				for (Entry<F17GAction, F17GType> e : gc.cases.entrySet())
				{
					// Could be partly factored out with above unary choice case (e.g., make an intermediate unary choice for recursive call)
					F17GAction ga = e.getKey();
					if (ga.getRoles().contains(r))
					{
						F17LType lt = project(e.getValue(), r, Collections.emptySet());
						F17LAction la = project(e.getKey(), r);
						if (la.isMessageAction())  // FIXME: factor out with below
						{
							if (gCases.keySet().stream().anyMatch((x) ->
									x.isMessageAction() && ((F17MessageAction) la).getOp().equals(((F17MessageAction) x).getOp())))
							{
								throw new F17SyntaxException("[f17] Non-determinism (" + r + ") not supported: " + gt);
							}
						}
						gCases.put(la, lt);
					}
					else
					{
						F17LType lt = project(e.getValue(), r, delta);
						if (lt instanceof F17LRecVar)
						{
							F17LRecVar grv = (F17LRecVar) lt;
							rvCases.put(ga, grv.var);
						}
						else if (lt instanceof F17LEnd)
						{
							eCases.add(ga);
						}
						else
						{

							if (!EXTENDED)
							{
								// Original
								if (!(lt instanceof F17LChoice) || ((F17LChoice) lt).cases.size() > 1)
								{
									throw new F17SyntaxException("[f17] Not projectable (non prefix-guarded case) onto " + r + ": " + lt);
								}
								Entry<F17LAction, F17LType> tmp = ((F17LChoice) lt).cases.entrySet().iterator().next();
								//if (gCases.containsKey(tmp.getKey()))
								if (tmp.getKey().isMessageAction())  // FIXME: factor out with above
								{
									if (gCases.keySet().stream().anyMatch((x) ->
											x.isMessageAction() && ((F17MessageAction) tmp.getKey()).getOp().equals(((F17MessageAction) x).getOp())))
									{
										throw new F17SyntaxException("[f17] Non-determinism (" + r + ") not supported: " + gt);
									}
								}
								gCases.put(tmp.getKey(), tmp.getValue());
							}
							else
							{
								// Extended -- needed for AppD
								if (lt instanceof F17LRec)
								{
									lt = ((F17LRec) lt).unfold();
								}
								if (!(lt instanceof F17LChoice))
								{
									throw new F17Exception("[f17] Not projectable (non prefix-guarded case) onto " + r + ": " + lt);  // Shouldn't get in here?
								}
								for (Entry<F17LAction, F17LType> tmp : ((F17LChoice) lt).cases.entrySet())  // Nested choice flattening
								{
									gCases.put(tmp.getKey(), tmp.getValue());
								}
							}

						}
					}
				}

				return (!EXTENDED)
						? orig(gc, r, delta, gCases, rvCases, eCases)
						: extended(gc, r, delta, gCases, rvCases, eCases);  // Doesn't seem needed for AppD though
			}
		}
		else if (gt instanceof F17GRec)
		{
			F17GRec gr = (F17GRec) gt;
			Set<RecVar> delta1 = new HashSet<>(delta);
			delta1.add(gr.recvar);
			F17LType lt = project(gr.body, r, delta1);
			if (lt instanceof F17LRecVar || lt instanceof F17LEnd)  //** end case (cf. orig)
			{
				return this.factory.LEnd();
			}
			return this.factory.LRec(gr.recvar, lt);
		}
		else if (gt instanceof F17GRecVar)
		{
			RecVar rv = ((F17GRecVar) gt).var;
			return this.factory.LRecVar(rv);
		}
		else if (gt instanceof F17GEnd)
		{
			return this.factory.LEnd();
		}
		else
		{
			throw new RuntimeException("[f17] Shouldn't get in here: " + gt);
		}
	}

	private F17LType extended(F17GChoice gc, Role r, Set<RecVar> delta,
			Map<F17LAction, F17LType> gCases, Map<F17GAction, RecVar> rvCases, Set<F17GAction> eCases) throws F17Exception
	{
		rvCases = rvCases.entrySet().stream().filter((e) -> !delta.contains(e.getValue()))
				.collect(Collectors.toMap((e) -> e.getKey(), (e) -> e.getValue()));

		if (gCases.isEmpty())
		{
			if (rvCases.isEmpty())
			{
				return this.factory.LEnd();
			}
			else
			{
				RecVar rv = rvCases.values().iterator().next();
				if (rvCases.values().stream().allMatch((v) -> v.equals(rv)))
				{
					return this.factory.LRecVar(rvCases.values().iterator().next());
				}
				else
				{
					throw new F17Exception("[f17] Cannot \"merge\" in projection onto " + r + ": " + rvCases.values());  // FIXME: src blame
				}
			}
		}
		else
		{
			if (!rvCases.isEmpty())
			{
				throw new F17Exception("[f17] Cannot project onto " + r + ": " + gc);  // FIXME: src blame
			}
			// Following same as "orig"
			F17LAction firsta = gCases.keySet().iterator().next();
			if (firsta.isOutput())  // Non- mixed-role choice subsumed by role enabling?
			{
				if (gCases.keySet().stream().anyMatch((k) -> !k.isOutput()))
				{
					throw new F17Exception("[f17] Inconsistent choice: " + gc);
				}
			}
			else  // firsta.isInput()
			{
				if (gCases.keySet().stream().anyMatch((k) -> !k.isInput()))
				{
					throw new F17Exception("[f17] Inconsistent choice: " + gc);
				}
				Role peer = ((F17LInput) firsta).peer;
				if (gCases.keySet().stream().anyMatch((k) -> !((F17LInput) k).peer.equals(peer)))
				{
					throw new F17Exception("[f17] Inconsistent input choice subjects: " + gc);  
							// subject means global action subjs (although also means peer in local)
							// N.B. consistent global choice subject (global internal choice subject, checked by role enabling) does not subsume this
				}
			}
			return this.factory.LChoice(gCases);
		}
	}

	//*
	private F17LType orig(F17GChoice gc, Role r, Set<RecVar> delta,
			Map<F17LAction, F17LType> gCases, Map<F17GAction, RecVar> rvCases, Set<F17GAction> eCases) throws F17Exception
	{
		if (!rvCases.isEmpty() && gCases.isEmpty() && eCases.isEmpty() && new HashSet<>(rvCases.values()).size() == 1)
		{
			return this.factory.LRecVar(rvCases.values().iterator().next());
		}
		else if (!eCases.isEmpty() && gCases.isEmpty() && rvCases.isEmpty())
		{
			return this.factory.LEnd();
		}
		else
		{
			for (RecVar rv : rvCases.values())
			{
				if (!delta.contains(rv))
				{
					throw new F17SyntaxException("[f17] Not projectable (unguarded rec case) onto " + r + ": " + rv);
				}
			}
			F17LAction firsta = gCases.keySet().iterator().next();
			if (firsta.isOutput())  // Non- mixed-role choice subsumed by role enabling?
			{
				if (gCases.keySet().stream().anyMatch((k) -> !k.isOutput()))
				{
					throw new F17Exception("[f17] Inconsistent choice: " + gc);
				}
			}
			else  // firsta.isInput()
			{
				if (gCases.keySet().stream().anyMatch((k) -> !k.isInput()))
				{
					throw new F17Exception("[f17] Inconsistent choice: " + gc);
				}
				Role peer = ((F17LInput) firsta).peer;
				if (gCases.keySet().stream().anyMatch((k) -> !((F17LInput) k).peer.equals(peer)))
				{
					throw new F17Exception("[f17] Inconsistent input choice subjects: " + gc);  
							// subject means global action subjs (although also means peer in local)
							// N.B. consistent global choice subject (global internal choice subject, checked by role enabling) does not subsume this
				}
			}
			return this.factory.LChoice(gCases);
		}
	}
	//*/

	public F17LAction project(F17GAction ga, Role r) throws F17Exception
	{
		if (!ga.getRoles().contains(r))
		{
			throw new RuntimeException("[f17] Shouldn't get in here: " + ga + ", " + r);
		}
		if (ga instanceof F17GMessageTransfer)
		{
			F17GMessageTransfer mt = (F17GMessageTransfer) ga;
			if (mt.src.equals(r))
			{
				return this.factory.LSend(r, mt.dest, mt.op, mt.pay);
			}
			else
			{
				return this.factory.LReceive(r, mt.src, mt.op, mt.pay);
			}
		}
		else if (ga instanceof F17GConnect)
		{
			F17GConnect c = (F17GConnect) ga;
			if (c.src.equals(r))
			{
				return this.factory.LConnect(r, c.dest, c.op, c.pay);
			}
			else
			{
				return this.factory.LAccept(r, c.src, c.op, c.pay);
			}
		}
		else if (ga instanceof F17GDisconnect)
		{
			F17GDisconnect d = (F17GDisconnect) ga;
			if (d.src.equals(r))
			{
				return this.factory.LDisconnect(r, d.dest);
			}
			else
			{
				return this.factory.LDisconnect(r, d.src);
			}
		}
		else
		{
			throw new RuntimeException("[f17] Shouldn't get in here: " + ga);
		}
	}
}
