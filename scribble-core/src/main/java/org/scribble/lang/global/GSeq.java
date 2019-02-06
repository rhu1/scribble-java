package org.scribble.lang.global;

import java.util.List;

import org.scribble.ast.global.GInteractionSeq;
import org.scribble.lang.Seq;
import org.scribble.type.kind.Global;

public class GSeq extends Seq<Global> implements GType
{
	// GInteractionSeq or GBlock better as source?
	public GSeq(GInteractionSeq source, List<GType> elems)
	{
		super(source, elems);
	}
	
	@Override
	public int hashCode()
	{
		int hash = 29;
		hash = 31 * hash + this.elems.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof GSeq))
		{
			return false;
		}
		return super.equals(o);  // Does canEquals
	}

	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof GSeq;
	}
}
