#!/usr/bin/env ruby

#require 'metasm'
#include Metasm
require 'digest'

module Utils
  refine String do
    # bin -> hex
    def to_hex
      self.unpack('C*').map {|x| "%2.2x" % x}.join
    end
    # hex -> bin
    def to_bin
      self.gsub(/\s+/, '').scan(/../).map {|x| x.to_i(16)}.pack('C*')
    end

    def byte_swap
      self.unpack('L*').pack('N*')
    end

    def to_dword
      self.unpack('L').shift
    end
  end

  refine Fixnum do

    BIT_WIDTH = 32
    BIT_MASK = (1 << BIT_WIDTH) - 1

    def rotl_32(shift)
      shift &= (BIT_WIDTH - 1)
      v = self & BIT_MASK
      ( (v << shift) | (v >> (BIT_WIDTH - shift)) ) & BIT_MASK
    end

    def rotr_32(shift)
      shift &= (BIT_WIDTH - 1)
      v = self & BIT_MASK
      ( (v >> shift) | (v << (BIT_WIDTH - shift)) ) & BIT_MASK
    end

    def bits_set
      ("%b" % self).count("1")
    end

  end
end

# Enable refinements
using Utils

# Basic RC5 implementation
class RC5

  P = 0xB7E15163
  Q = 0x9E3779B9

  BIT_WIDTH = 32
  BIT_MASK = (1 << BIT_WIDTH) - 1

  def initialize(key, rounds = 12)
    @key = key
    @rounds = rounds
    @t = 2 * (@rounds + 1)
    setup
  end

  def setup
    @L = @key.unpack('L*')
    @c = @L.size
    @S = Array.new(@t, 0)
    @S[0] = P
    (1..@t-1).each do |i|
      @S[i] = (@S[i-1] + Q) & BIT_MASK
    end

    i = j = 0
    _A = _B = 0
    (3*@t).times do |k|
      _A = @S[i] = (@S[i] + _A + _B).rotl_32(3)
      _B = @L[j] = (@L[j] + _A + _B).rotl_32(_A + _B)
      i = (i + 1) % @t
      j = (j + 1) % @c
    end
  end

  def encrypt_words(w0, w1)
    _A = (w0 + @S[0]) & BIT_MASK
    _B = (w1 + @S[1]) & BIT_MASK
    (1..@rounds).each do |i|
      _A = (_A ^ _B).rotl_32(_B) + @S[2 * i]
      _A &= BIT_MASK
      _B = (_B ^ _A).rotl_32(_A) + @S[2 * i + 1]
      _B &= BIT_MASK
    end
    return [_A, _B]
  end

  def decrypt_words(w0, w1)
    _A = w0
    _B = w1
    (1..@rounds).reverse_each do |i|
      _B = (_B - @S[2 * i + 1]).rotr_32(_A) ^ _A
      _A = (_A - @S[2 * i]).rotr_32(_B) ^ _B
    end
    _B = (_B - @S[1]) & BIT_MASK
    _A = (_A - @S[0]) & BIT_MASK
    return [_A, _B]
  end

  def encrypt_hex(s)
    sbin = s.to_bin
    raise "needs padding" if sbin.size % 8 != 0
    words = sbin.unpack('L*')
    res = []
    while not words.empty?
      w0, w1 = words.shift, words.shift
      w0, w1 = encrypt_words(w0, w1)
      res << w0 << w1
    end
    return res.pack('L*').to_hex
  end

  def decrypt_hex(s)
    sbin = s.to_bin
    raise "needs padding" if sbin.size % 8 != 0
    words = sbin.unpack('L*')
    res = []
    while not words.empty?
      w0, w1 = words.shift, words.shift
      w0, w1 = decrypt_words(w0, w1)
      res << w0 << w1
    end
    return res.pack('L*').to_hex
  end

  class << self
    def unit_test(key, rounds, cipher, plain)
      rc5 = self.new(key.to_bin, rounds)
      raise "wrong encrypt" if rc5.encrypt_hex(plain).downcase != cipher.downcase
      raise "wrong decrypt" if rc5.decrypt_hex(cipher).downcase != plain.downcase
    end
    def self_test
      # Vector from Cryptograph execution, first derived rc5 key
      unit_test("18341F0D04ADF17CBEAF44A61ABFDEEB", 15, "D78C42D990E7344B", "58C47255B1615233")
      # Standard test vector
      unit_test("80000000000000000000000000000000", 12, "8F681D7F285CDC2F", "0000000000000000")
    end
  end

end

class FlareMD5 < Digest::MD5
  # reverse byte order
  def finish
    res = super
    res.byte_swap
  end
end

class HMAC < Digest::Class

  def initialize(key, digester)
    @md = digester.new

    block_len = @md.block_length

    ipad = Array.new(block_len, 0x36)
    opad = Array.new(block_len, 0x5c)

    key.bytes.each_with_index do |c, i|
      ipad[i] ^= c
      opad[i] ^= c
    end

    @key = key.freeze
    @ipad = ipad.pack('C*').freeze
    @opad = opad.pack('C*').freeze
    @md.update(@ipad)
  end

  def update(text)
    @md.update(text)
    self
  end
  alias << update

  def reset
    @md.reset
    @md.update(@ipad)
    self
  end

  def finish
    d = @md.digest!
    @md.update(@opad)
    @md.update(d)
    @md.digest!
  end

  def digest_length
    @md.digest_length
  end

  def block_length
    @md.block_length
  end

  class << self
    def unit_test(key, data, hexdigest)
      hmac = self.new(key, Digest::MD5)
      hmac << data
      digest = hmac.digest.to_hex
      raise "wrong result" if digest.downcase != hexdigest
    end

    def self_test
      unit_test("\xaa" * 16, "\xdd" * 50, "56be34521d144c88dbb8c733f0e8b3f6")
      unit_test("Jefe", "what do ya want for nothing?", "750c783e6ab0b503eaa86e310a5db738")
    end
  end

end

class Block
  attr_reader :iter_count, :key, :message, :crypted

  def initialize(idx, rc5_rounds, crypted)
    @idx = idx
    @rc5_rounds = rc5_rounds
    @crypted = crypted
    @rc5_iter = (@idx > 0) ? 1.rotl_32(@idx) + 1 : 1
  end

  def parse_plaintext(plaintext)
    @block_number = plaintext[ 0,  4].to_dword
    raise "wrong block number" if @block_number != @idx

    @iter_count   = plaintext[ 4,  4].to_dword
    @key          = plaintext[ 8,  8]
    @message      = plaintext[16, 16]
    @md5sum       = plaintext[32, 16]

    calc_md5 = FlareMD5.digest(plaintext[0, 32])
    raise "wrong md5" if calc_md5 != @md5sum
  end

  def to_s
    "[#@idx] iter: 0x%8.8x, key: %s, message: %s" % [ @iter_count, @key.to_hex, @message.to_hex ]
  end
end

class CryptoGraph

  RES_INFOS = {
    120 => { offset: 0x160b0, size: 0x48},
    121 => { offset: 0x15980, size: 0x630},
    122 => { offset: 0x15fb0, size: 0x100},
    124 => { offset: 0x234a8, size: 0x10040}
  }

  attr_reader :round_infos
  def initialize(pe_path)
    @pe_path = pe_path
    load_data
    setup
  end

  def load_data
    File.open(@pe_path, "rb") do |f|
      RES_INFOS.each do |res_id, res_infos|
        f.seek(res_infos[:offset], IO::SEEK_SET)
        data = f.read(res_infos[:size])
        instance_variable_set("@r#{res_id}_data", data)
      end
    end
  end

  def setup
    r1 = @r120_data[ 0, 16].unpack('Q2')
    r2 = @r120_data[16, 16].unpack('Q2')
    r3 = @r120_data[32, 16].unpack('Q2')

    @init_key = [ r1, r2, r3 ].transpose.map {|x, y, z| x ^ y ^ z}.pack('Q2')
    @header       = @r121_data[0, 8]
    @iter         = @r121_data[8, 4].to_dword
    @rc5_rounds   = @r121_data[12, 4].to_dword
    @init_message = @r121_data[16, 16].unpack('C*')
    @md5sum       = @r121_data[32, 16]
    @blocks = []
    32.times do |i|
      @blocks << Block.new(i, @rc5_rounds, @r121_data[48 + 48 * i, 48])
    end
  end

  # sub_4014E0
  def calc_rc5_key(key, message, iter_count, val)
    expanded_message = message + [ val ].pack('N')
    mac = HMAC.new(key, FlareMD5)

    mac << expanded_message
    prev_hmac = mac.digest

    (iter_count - 1).times do |i|
      mac.reset
      mac << prev_hmac
      curr_hmac = mac.digest

      qw0, qw1 = prev_hmac.unpack('Q2'), curr_hmac.unpack('Q2')
      prev_hmac = [ qw0, qw1 ].transpose.map {|x,y| x ^ y}.pack('Q2')
    end
    return prev_hmac
  end

  # sub_402BE0
  def decrypt_data(rc5, crypted, y0, y1)
    raise "needs padding" if crypted.size % 8 != 0
    ct = crypted.unpack('L*')
    iter = ct.size / 2 - 1
    (0..iter).reverse_each do |i|
      pt0, pt1 = rc5.decrypt_words(ct[2*i], ct[2*i+1])
      x0 = i > 0 ? ct[2*(i-1)]   : y0
      x1 = i > 0 ? ct[2*(i-1)+1] : y1
      ct[2*i]   = pt0 ^ x0
      ct[2*i+1] = pt1 ^ x1
    end
    ct.pack('L*')
  end

  # sub_4015D0
  def decrypt_blocks(count = 31)
    @init_message[0] |= 205

    key = @init_key
    message = @init_message.pack('C*')
    rc5_iter = 1

    (0..count).each do |b_idx|
      bl = @blocks[b_idx]

      rc5_key = calc_rc5_key(FlareMD5.digest(key), message, @iter, 1)
      rc5 = RC5.new(rc5_key, @rc5_rounds + b_idx)

      crypted = bl.crypted
      rc5_iter.times do
        crypted = decrypt_data(rc5, crypted, b_idx + 1, b_idx + 1)
      end
      bl.parse_plaintext(crypted)

      puts bl

      key, message = bl.key, bl.message
      @iter = bl.iter_count + @iter * (b_idx >> 4)
      rc5_iter = 1.rotl_32(b_idx+1) + 1
    end
  end

  # sub_401CF0
  def write_file(idx, out = 'secret.jpg')
    bl = @blocks[idx]
    raise "not enough blocks decrypted" unless bl.key

    rc5 = RC5.new(bl.key, idx + 2 * @rc5_rounds)
    rc5_key = decrypt_data(rc5, @r122_data[16 * idx, 16], idx, idx)

    rc5 = RC5.new(rc5_key, 15)
    r124_size = RES_INFOS[124][:size]
    plaintext = decrypt_data(rc5, @r124_data, r124_size, r124_size)

    File.open(out, "wb") { |f| f.write plaintext }
    puts "[*] File written to #{out}"
  end

  def solve
    dwords = @init_key.unpack('L4')
    idx = (dwords[1] | 16).bits_set / 2
    decrypt_blocks(idx)
    write_file(idx)
  end

end

RC5.self_test ; HMAC.self_test

cp = CryptoGraph.new(ARGV.shift || 'CryptoGraph.exe')
cp.solve
