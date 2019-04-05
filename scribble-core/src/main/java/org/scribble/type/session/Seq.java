/**
 * Copyright 2008 The Scribble Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */
package org.scribble.type.session;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.type.kind.ProtocolKind;
import org.scribble.type.name.MemberName;
import org.scribble.type.name.MessageId;
import org.scribble.type.name.ProtocolName;
import org.scribble.type.name.RecVar;
import org.scribble.type.name.Role;
import org.scribble.type.name.Substitutions;
import org.scribble.visit.STypeInliner;
import org.scribble.visit.STypeUnfolder;

// Could add B extends STypeBase, but it inflates type params quite a bit (e.g., Protocol)
public abstract class Seq<K extends ProtocolKind>
		extends STypeBase<K>
{
	public final List<? extends SType<K>> elems;  // GType or LType

	public Seq(CommonTree source, List<? extends SType<K>> elems)
	{
		super(source);
		this.elems = Collections.unmodifiableList(elems);
	}
	
	public abstract Seq<K> reconstruct(CommonTree source,
			List<? extends SType<K>> elems);

	@Override
	public Set<Role> getRoles()
	{
		return this.elems.stream().flatMap(x -> x.getRoles().stream())
				.collect(Collectors.toSet());
	}

	@Override
	public Set<MessageId<?>> getMessageIds()
	{
		return this.elems.stream().flatMap(x -> x.getMessageIds().stream())
				.collect(Collectors.toSet());
	}
	
	@Override
	public Set<RecVar> getRecVars()
	{
		return this.elems.stream().flatMap(x -> x.getRecVars().stream())
				.collect(Collectors.toSet());
	}

	@Override
	public Seq<K> substitute(Substitutions subs)
	{
		List<? extends SType<K>> elems = this.elems.stream()
				.map(x -> x.substitute(subs)).collect(Collectors.toList());
		return reconstruct(getSource(), elems);
	}

	@Override
	public Seq<K> getInlined(STypeInliner v)
	{
		CommonTree source = getSource(); // CHECKME: or empty source?
		List<SType<K>> elems = new LinkedList<>();
		for (SType<K> e : this.elems)
		{
			SType<K> e1 = e.getInlined(v);
			if (e1 instanceof Seq<?>)
			{
				elems.addAll(((Seq<K>) e1).elems); // Inline Seq's returned by Do.getInlined
			}
			else
			{
				elems.add(e1);
			}
		}
		return reconstruct(source, elems);
	}

	@Override
	public Seq<K> unfoldAllOnce(STypeUnfolder<K> u)
	{
		CommonTree source = getSource();
		List<SType<K>> elems = new LinkedList<>();
		for (SType<K> e : this.elems)
		{
			SType<K> e1 = e.unfoldAllOnce(u);
			if (e1 instanceof Seq<?>)
			{
				elems.addAll(((Seq<K>) e1).elems);
			}
			else
			{
				elems.add(e1);
			}
		}
		return reconstruct(source, elems);
	}
		
	@Override
	public List<ProtocolName<K>> getProtoDependencies()
	{
		return this.elems.stream().flatMap(x -> x.getProtoDependencies().stream())
				.distinct().collect(Collectors.toList());
	}

	@Override
	public List<MemberName<?>> getNonProtoDependencies()
	{
		return this.elems.stream()
				.flatMap(x -> x.getNonProtoDependencies().stream()).distinct()
				.collect(Collectors.toList());
	}

	public abstract List<? extends SType<K>> getElements();
	
	public boolean isEmpty()
	{
		return this.elems.isEmpty();
	}
	
	@Override
	public String toString()
	{
		return this.elems.stream().map(x -> x.toString())
				.collect(Collectors.joining("\n"));
	}

	@Override
	public int hashCode()
	{
		int hash = 1483;
		hash = 31 * hash + super.hashCode();
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
		if (!(o instanceof Seq))
		{
			return false;
		}
		Seq<?> them = (Seq<?>) o;
		return super.equals(this)  // Does canEquals
				&& this.elems.equals(them.elems);
	}
}
