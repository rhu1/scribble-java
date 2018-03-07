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
package org.scribble.runtime.net.state;

import org.scribble.runtime.net.ScribMessage;
import org.scribble.type.name.Role;

@Deprecated
public class ScribEvent<R extends Role, M extends ScribHandlerMessage> extends ScribMessage
{
	private static final long serialVersionUID = 1L;

	public final R peer;

	//public ScribEvent(Role peer, Op op, Object... payload)  // FIXME: factor out with EAction?
	public ScribEvent(R peer, M m)  // FIXME: factor out with EAction?
	{
		super(m.getOp(), m.getPayload());
		this.peer = peer;
	}
	
	@Override
	public int hashCode()
	{
		int hash = 7919;
		hash = 31 * hash + super.hashCode();
		hash = 31 * hash + this.peer.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof ScribEvent))
		{
			return false;
		}
		ScribEvent<?, ?> m = (ScribEvent<?, ?>) o;
		return super.equals(o) && this.peer.equals(m.peer);  // Does canEqual
	}
	
	@Override
	public boolean canEqual(Object o)
	{
		return o instanceof ScribEvent;
	}
	
	@Override
	public String toString()
	{
		return this.peer + ":" + super.toString();
	}
}