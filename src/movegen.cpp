/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2025 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "movegen.h"

#include <cassert>
#include <initializer_list>

#include "bitboard.h"
#include "position.h"

namespace Stockfish {

namespace {

template<GenType Type, Direction D, bool Enemy>
ExtMove* make_promotions(ExtMove* moveList, [[maybe_unused]] Square to) {

    constexpr bool all = Type == EVASIONS || Type == NON_EVASIONS;

    if constexpr (Type == CAPTURES || all)
        *moveList++ = Move::make<PROMOTION>(to - D, to, QUEEN);

    if constexpr ((Type == CAPTURES && Enemy) || (Type == QUIETS && !Enemy) || all)
    {
        *moveList++ = Move::make<PROMOTION>(to - D, to, ROOK);
        *moveList++ = Move::make<PROMOTION>(to - D, to, BISHOP);
        *moveList++ = Move::make<PROMOTION>(to - D, to, KNIGHT);
    }

    return moveList;
}


template<Color Us, GenType Type>
ExtMove* generate_pawn_moves(const Position& pos, ExtMove* moveList, Bitboard target) {

    constexpr Color     Them     = ~Us;
    constexpr Bitboard  TRank7BB = (Us == WHITE ? Rank7BB : Rank2BB);
    constexpr Bitboard  TRank3BB = (Us == WHITE ? Rank3BB : Rank6BB);
    constexpr Direction Up       = pawn_push(Us);
    constexpr Direction UpRight  = (Us == WHITE ? NORTH_EAST : SOUTH_WEST);
    constexpr Direction UpLeft   = (Us == WHITE ? NORTH_WEST : SOUTH_EAST);

    const Bitboard pawns        = pos.pieces(Us, PAWN);
    const Bitboard emptySquares = ~pos.pieces();
    const Bitboard enemies      = Type == EVASIONS ? pos.checkers() : pos.pieces(Them);
    
    // Pre-calculate seventh rank pawns and the rest
    const Bitboard pawnsOn7    = pawns & TRank7BB;
    const Bitboard pawnsNotOn7 = pawns & ~TRank7BB;

    // Handle non-capture moves (if applicable)
    if constexpr (Type != CAPTURES) {
        Bitboard b1 = shift<Up>(pawnsNotOn7) & emptySquares;
        Bitboard b2 = shift<Up>(b1 & TRank3BB) & emptySquares;

        if constexpr (Type == EVASIONS) {
            b1 &= target;
            b2 &= target;
        }

        while (b1) {
            Square to = pop_lsb(b1);
            *moveList++ = Move(to - Up, to);
        }

        while (b2) {
            Square to = pop_lsb(b2);
            *moveList++ = Move(to - Up - Up, to);
        }
    }

    // Handle promotions efficiently - combine similar operations
    if (pawnsOn7) {
        Bitboard promoAttacks = ((shift<UpRight>(pawnsOn7) | shift<UpLeft>(pawnsOn7)) & enemies) 
                             | (shift<Up>(pawnsOn7) & emptySquares & (Type == EVASIONS ? target : ~Bitboard(0)));

        while (promoAttacks) {
            Square to = pop_lsb(promoAttacks);
            
            // Split promotion moves by type to avoid potential race conditions
            Bitboard rightAttacks = shift<UpRight>(pawnsOn7) & enemies;
            Bitboard leftAttacks = shift<UpLeft>(pawnsOn7) & enemies;
            
            if (rightAttacks & square_bb(to))
                moveList = make_promotions<Type, UpRight, true>(moveList, to);
            else if (leftAttacks & square_bb(to))
                moveList = make_promotions<Type, UpLeft, true>(moveList, to);
            else
                moveList = make_promotions<Type, Up, false>(moveList, to);
        }
    }

    // Handle standard captures and en passant in one block
    if constexpr (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS) {
        Bitboard rightCaptures = shift<UpRight>(pawnsNotOn7) & enemies;
        Bitboard leftCaptures = shift<UpLeft>(pawnsNotOn7) & enemies;

        while (rightCaptures) {
            Square to = pop_lsb(rightCaptures);
            *moveList++ = Move(to - UpRight, to);
        }

        while (leftCaptures) {
            Square to = pop_lsb(leftCaptures);
            *moveList++ = Move(to - UpLeft, to);
        }

        if (pos.ep_square() != SQ_NONE) {
            assert(rank_of(pos.ep_square()) == relative_rank(Us, RANK_6));

            if (!(Type == EVASIONS && (target & (pos.ep_square() + Up)))) {
                Bitboard epCaptures = pawnsNotOn7 & attacks_bb<PAWN>(pos.ep_square(), Them);
                while (epCaptures)
                    *moveList++ = Move::make<EN_PASSANT>(pop_lsb(epCaptures), pos.ep_square());
            }
        }
    }

    return moveList;
}


template<Color Us, PieceType Pt>
ExtMove* generate_moves(const Position& pos, ExtMove* moveList, Bitboard target) {

    static_assert(Pt != KING && Pt != PAWN, "Unsupported piece type in generate_moves()");

    const Bitboard pieces = pos.pieces(Us, Pt);
    const Bitboard occupied = pos.pieces();

    Bitboard bb = pieces;
    while (bb) {
        Square from = pop_lsb(bb);
        Bitboard attacks = attacks_bb<Pt>(from, occupied) & target;
            
        while (attacks)
            *moveList++ = Move(from, pop_lsb(attacks));
    }

    return moveList;
}


template<Color Us, GenType Type>
ExtMove* generate_all(const Position& pos, ExtMove* moveList) {

    static_assert(Type != LEGAL, "Unsupported type in generate_all()");

    const Square ksq = pos.square<KING>(Us);
    
    // Pre-calculate target bitboard - this avoids recalculating for each piece type
    const Bitboard target = Type == EVASIONS     ? between_bb(ksq, lsb(pos.checkers()))
                         : Type == NON_EVASIONS ? ~pos.pieces(Us)
                         : Type == CAPTURES     ? pos.pieces(~Us)
                         : ~pos.pieces();  // QUIETS

    // Skip generating moves when in double check - only king moves are legal
    if (Type != EVASIONS || !more_than_one(pos.checkers())) {
        // Generate moves for all piece types in one pass
        moveList = generate_pawn_moves<Us, Type>(pos, moveList, target);
        
        // Generate piece moves in order of likelihood of being useful
        // Knights first as they're less likely to be pinned
        moveList = generate_moves<Us, KNIGHT>(pos, moveList, target);
        moveList = generate_moves<Us, BISHOP>(pos, moveList, target);
        moveList = generate_moves<Us, ROOK>(pos, moveList, target);
        moveList = generate_moves<Us, QUEEN>(pos, moveList, target);
    }

    // Generate king moves - combine normal moves and castling in one pass
    Bitboard kingMoves = attacks_bb<KING>(ksq) & (Type == EVASIONS ? ~pos.pieces(Us) : target);
    
    while (kingMoves)
        *moveList++ = Move(ksq, pop_lsb(kingMoves));

    // Handle castling in non-capture and non-evasion modes
    if ((Type == QUIETS || Type == NON_EVASIONS) && pos.can_castle(Us & ANY_CASTLING)) {
        for (CastlingRights cr : {Us & KING_SIDE, Us & QUEEN_SIDE}) {
            if (!pos.castling_impeded(cr) && pos.can_castle(cr))
                *moveList++ = Move::make<CASTLING>(ksq, pos.castling_rook_square(cr));
        }
    }

    return moveList;
}

}  // namespace


// <CAPTURES>     Generates all pseudo-legal captures plus queen promotions
// <QUIETS>       Generates all pseudo-legal non-captures and underpromotions
// <EVASIONS>     Generates all pseudo-legal check evasions
// <NON_EVASIONS> Generates all pseudo-legal captures and non-captures
//
// Returns a pointer to the end of the move list.
template<GenType Type>
ExtMove* generate(const Position& pos, ExtMove* moveList) {

    static_assert(Type != LEGAL, "Unsupported type in generate()");
    assert((Type == EVASIONS) == bool(pos.checkers()));

    Color us = pos.side_to_move();

    return us == WHITE ? generate_all<WHITE, Type>(pos, moveList)
                       : generate_all<BLACK, Type>(pos, moveList);
}

// Explicit template instantiations
template ExtMove* generate<CAPTURES>(const Position&, ExtMove*);
template ExtMove* generate<QUIETS>(const Position&, ExtMove*);
template ExtMove* generate<EVASIONS>(const Position&, ExtMove*);
template ExtMove* generate<NON_EVASIONS>(const Position&, ExtMove*);


// Generates all the legal moves in the given position

template<>
ExtMove* generate<LEGAL>(const Position& pos, ExtMove* moveList) {
    const Color us = pos.side_to_move();
    const Bitboard pinned = pos.blockers_for_king(us) & pos.pieces(us);
    const Square ksq = pos.square<KING>(us);
    ExtMove* cur = moveList;
    
    // Generate pseudo-legal moves
    moveList = pos.checkers() ? generate<EVASIONS>(pos, moveList) 
                             : generate<NON_EVASIONS>(pos, moveList);

    // Filter out illegal moves
    while (cur != moveList) {
        const bool needsLegalityCheck = (pinned & cur->from_sq()) || 
                                      cur->from_sq() == ksq || 
                                      cur->type_of() == EN_PASSANT;
        
        if (needsLegalityCheck && !pos.legal(*cur))
            *cur = *(--moveList);
        else
            ++cur;
    }

    return moveList;
}

}  // namespace Stockfish
