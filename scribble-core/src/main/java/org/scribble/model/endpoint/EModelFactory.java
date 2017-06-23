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
package org.scribble.model.endpoint;

import java.util.Set;

import org.scribble.model.endpoint.actions.EAccept;
import org.scribble.model.endpoint.actions.EConnect;
import org.scribble.model.endpoint.actions.EReceive;
import org.scribble.model.endpoint.actions.ESend;
import org.scribble.sesstype.Payload;
import org.scribble.sesstype.name.MessageId;
import org.scribble.sesstype.name.RecVar;
import org.scribble.sesstype.name.Role;

public interface EModelFactory
{
	EConnect newEConnect(Role peer, MessageId<?> mid, Payload payload);
	EAccept newEAccpt(Role peer, MessageId<?> mid, Payload payload);
	ESend newESend(Role peer, MessageId<?> mid, Payload payload);
	EReceive newEReceive(Role peer, MessageId<?> mid, Payload payload);

	EState newEState(Set<RecVar> labs);
}
