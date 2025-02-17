{-
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/cql`, the categorical query language.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}
{-# LANGUAGE DerivingStrategies #-}
module Api.Config.Environment where

-- wai
import           Network.Wai                          (Middleware)

-- wai-extra
import           Network.Wai.Middleware.RequestLogger (logStdout, logStdoutDev)

data Environment
  = Development
  | Production
  deriving stock (Show, Read)

logger :: Environment -> Middleware
logger Development = logStdoutDev
logger Production  = logStdout
