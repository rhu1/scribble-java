package org.scribble.core.visit;

import java.util.stream.Stream;

import org.scribble.core.type.kind.ProtocolKind;
import org.scribble.core.type.name.ProtocolName;
import org.scribble.core.type.session.Choice;
import org.scribble.core.type.session.Continue;
import org.scribble.core.type.session.DirectedInteraction;
import org.scribble.core.type.session.DisconnectAction;
import org.scribble.core.type.session.Do;
import org.scribble.core.type.session.Recursion;
import org.scribble.core.type.session.Seq;

// Visitor could be refactored as an Agg, but not worth it?  (unit = n.getChildren(), agg = reconstruct)
public abstract class STypeAgg<K extends ProtocolKind, B extends Seq<K, B>, T>
{
	public abstract T unit();
	public abstract T agg(Stream<T> ts);  // Generic varargs has heap pollution issue
	
	// SType return for extensibility/flexibility
	public T visitContinue(Continue<K, B> n)
	{
		return agg(Stream.of(unit()));
	}

	public T visitChoice(Choice<K, B> n)
	{
		return agg(n.blocks.stream().map(x -> x.aggregate(this)));
	}

	public T visitDirectedInteraction(DirectedInteraction<K, B> n)
	{
		return agg(Stream.of(unit()));
	}

	public T visitDisconnect(DisconnectAction<K, B> n)
	{
		return agg(Stream.of(unit()));
	}

	public <N extends ProtocolName<K>> T visitDo(Do<K, B, N> n)
	{
		return agg(Stream.of(unit()));
	}

	public T visitRecursion(Recursion<K, B> n)
	{
		return agg(Stream.of(n.body.aggregate(this)));
	}

	// "Hardcoded" to B (cf. Seq, or SType return) -- this visitor pattern depends on B for Choice/Recursion/etc reconstruction
	public T visitSeq(B n)
	{
		return agg(n.elems.stream().map(x -> x.aggregate(this)));
	}
}




















/*@FunctionalInterface
interface STypeVisitorFunction<K extends ProtocolKind, B extends Seq<K, B>, R extends Stream<?>>
{
	R f(SType<K, B> n, STypeVisitor<K, B> v);
}*/
