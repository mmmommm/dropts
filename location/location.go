package location

import (
	"strings"
	"unicode/utf8"
)

type Loc struct {
	// This is the 0-based index of this location from the start of the file, in bytes
	Start int32
}

type Range struct {
	Loc Loc
	Len int32
}

func (r Range) End() int32 {
	return r.Loc.Start + r.Len
}

type Span struct {
	Text  string
	Range Range
}

// This is used to represent both file system paths (Namespace == "file") and
// abstract module paths (Namespace != "file"). Abstract module paths represent
// "virtual modules" when used for an input file and "package paths" when used
// to represent an external module.
// type Path struct {
// 	Text      string
// 	Namespace string

// 	// This feature was added to support ancient CSS libraries that append things
// 	// like "?#iefix" and "#icons" to some of their import paths as a hack for IE6.
// 	// The intent is for these suffix parts to be ignored but passed through to
// 	// the output. This is supported by other bundlers, so we also support this.
// 	IgnoredSuffix string

// 	Flags PathFlags
// }

// type PathFlags uint8


type Source struct {
	// This is used for error messages and the metadata JSON file.
	//
	// This is a mostly platform-independent path. It's relative to the current
	// working directory and always uses standard path separators. Use this for
	// referencing a file in all output data. These paths still use the original
	// case of the path so they may still work differently on file systems that
	// are case-insensitive vs. case-sensitive.
	// PrettyPath string

	// An identifier that is mixed in to automatically-generated symbol names to
	// improve readability. For example, if the identifier is "util" then the
	// symbol for an "export default" statement will be called "util_default".
	IdentifierName string

	Contents string

	// This is used as a unique key to identify this source file. It should never
	// be shown to the user (e.g. never print this to the terminal).
	//
	// If it's marked as an absolute path, it's a platform-dependent path that
	// includes environment-specific things such as Windows backslash path
	// separators and potentially the user's home directory. Only use this for
	// passing to syscalls for reading and writing to the file system. Do not
	// include this in any output data.
	//
	// If it's marked as not an absolute path, it's an opaque string that is used
	// to refer to an automatically-generated module.
	// KeyPath Path

	Index uint32
}

func (s *Source) TextForRange(r Range) string {
	return s.Contents[r.Loc.Start : r.Loc.Start+r.Len]
}

func (s *Source) LocBeforeWhitespace(loc Loc) Loc {
	for loc.Start > 0 {
		c, width := utf8.DecodeLastRuneInString(s.Contents[:loc.Start])
		if c != ' ' && c != '\t' && c != '\r' && c != '\n' {
			break
		}
		loc.Start -= int32(width)
	}
	return loc
}

func (s *Source) RangeOfOperatorBefore(loc Loc, op string) Range {
	text := s.Contents[:loc.Start]
	index := strings.LastIndex(text, op)
	if index >= 0 {
		return Range{Loc: Loc{Start: int32(index)}, Len: int32(len(op))}
	}
	return Range{Loc: loc}
}

func (s *Source) RangeOfOperatorAfter(loc Loc, op string) Range {
	text := s.Contents[loc.Start:]
	index := strings.Index(text, op)
	if index >= 0 {
		return Range{Loc: Loc{Start: loc.Start + int32(index)}, Len: int32(len(op))}
	}
	return Range{Loc: loc}
}

func (s *Source) RangeOfString(loc Loc) Range {
	text := s.Contents[loc.Start:]
	if len(text) == 0 {
		return Range{Loc: loc, Len: 0}
	}

	quote := text[0]
	if quote == '"' || quote == '\'' {
		// Search for the matching quote character
		for i := 1; i < len(text); i++ {
			c := text[i]
			if c == quote {
				return Range{Loc: loc, Len: int32(i + 1)}
			} else if c == '\\' {
				i += 1
			}
		}
	}

	return Range{Loc: loc, Len: 0}
}

func (s *Source) RangeOfNumber(loc Loc) (r Range) {
	text := s.Contents[loc.Start:]
	r = Range{Loc: loc, Len: 0}

	if len(text) > 0 {
		if c := text[0]; c >= '0' && c <= '9' {
			r.Len = 1
			for int(r.Len) < len(text) {
				c := text[r.Len]
				if (c < '0' || c > '9') && (c < 'a' || c > 'z') && (c < 'A' || c > 'Z') && c != '.' && c != '_' {
					break
				}
				r.Len++
			}
		}
	}
	return
}

func (s *Source) RangeOfLegacyOctalEscape(loc Loc) (r Range) {
	text := s.Contents[loc.Start:]
	r = Range{Loc: loc, Len: 0}

	if len(text) >= 2 && text[0] == '\\' {
		r.Len = 2
		for r.Len < 4 && int(r.Len) < len(text) {
			c := text[r.Len]
			if c < '0' || c > '9' {
				break
			}
			r.Len++
		}
	}
	return
}

func PlatformIndependentPathDirBaseExt(path string) (dir string, base string, ext string) {
	for {
		i := strings.LastIndexAny(path, "/\\")

		// Stop if there are no more slashes
		if i < 0 {
			base = path
			break
		}

		// Stop if we found a non-trailing slash
		if i+1 != len(path) {
			dir, base = path[:i], path[i+1:]
			break
		}

		// Ignore trailing slashes
		path = path[:i]
	}

	// Strip off the extension
	if dot := strings.LastIndexByte(base, '.'); dot >= 0 {
		base, ext = base[:dot], base[dot:]
	}

	return
}