package helpers

import (
	"sync"
	"github.com/mmmommm/dropts/logger"
)

const SourceIndex = uint32(0)

type SourceIndexCache struct {
	mutex           sync.Mutex
	entries         map[sourceIndexKey]uint32
	nextSourceIndex uint32
}

type SourceIndexKind uint8

const (
	SourceIndexNormal SourceIndexKind = iota
	SourceIndexJSStubForCSS
)

type sourceIndexKey struct {
	path logger.Path
	kind SourceIndexKind
}
