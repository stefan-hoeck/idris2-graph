module Main

import Hedgehog
import BitMap

main : IO ()
main = test [ BitMap.props
            ]
